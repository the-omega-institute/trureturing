# Native variable-coefficient Green stability on the fixed two-wall cylinder

This companion completes the fixed-model question left open at the end of
the original Green volume. It keeps the source, the killed cylinder, the
actual phase torus, the two native horizontal controls, and the full
unit-source Green field of Definition 1.3. Only the smooth positive density
and the positive definite horizontal covariance are allowed to vary. The
claims are ordinary mathematical statements; they are not Lean declarations.

## 1. Fixed model and the exact question

Fix the native means and the preparation data before choosing any analytic
object. Let $r=1-Z$ and let $J_b$ and the grouped pole construction be as in
[N, Definitions 2.1, 3.1 and 8.1](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md).
For a fixed open interval $I=(l,u)\Subset J_b$, put

$$
\Omega=I\times\mathbb T^m,
\qquad P=\partial_k,
\qquad Q=\sum_{a=1}^m w_a(k)\partial_{h_a}.
$$

The two walls are $E_- = \{X+Y=r\}$ and $E_+=\{X=Y\}$. Their native
classification is

$$
\begin{array}{c|c|c|c|c}
\text{walls}&\text{current-ray dim.}&\text{direct rank}&\text{growth}&Q_{\rm vol}\\ \hline
\text{neither}&5&2&(2,3,4,5)&11\\
\text{one}&4&2&(2,3,4)&7\\
\text{both}&3&2&(2,3)&4.
\end{array}
$$

Here and below $Q_{\rm vol}$ is the homogeneous volume exponent of the
native horizontal operator, not the vector field named $Q$.

Choose a real smooth positive density $\rho$ and a real smooth symmetric
positive definite matrix $A=(a^{ij})_{1\leq i,j\leq2}$ on a neighbourhood
of $\overline\Omega$. With $d\mu=\rho\,dk\,dh$, define

$$
T_A[f]=\int_\Omega \sum_{i,j}a^{ij}(X_jf)\overline{X_if}\,d\mu,
\qquad
\mathcal F_A=\overline{C_c^\infty(\Omega)}^{\,\|f\|_2^2+T_A[f]}.
\tag{1.1}
$$

The boundary is periodic in each actual phase and killed at $k=l,u$. Let
$L_A$ be the operator represented by this closed form and let
$\Gamma_{A,o}$ be the full killed Green field of $L_A$ with one source at
$o\in\Omega$, exactly as in Definition 1.3 of the original volume. Thus

$$
V_{A,o}[f]=\int_\Omega\Gamma_{A,o}|f|^2\,d\mu,
\qquad
q_{A,g}[f]=T_A[f]-gV_{A,o}[f],\quad g>0.
\tag{1.2}
$$

The source is not averaged over the torus and the Green field is not cut off
in time. The clock is still $e^{-tL_A}$, so the control covariance remains
$2A\,dt$.

The target is the following fixed-model assertion: there is a nonempty
interval of positive $g$ for which $q_{A,g}$ is closed and semibounded on
exactly $\mathcal F_A$, has an equivalent shifted form norm, compact
resolvent, and an attained normalized minimum, if and only if both native
walls hold. In the both-wall case we also seek a finite sufficient value of
$g$ above which the same full Green form collapses to $-\infty$.

## 2. Native double-wall coordinates

Assume both walls. The two grouped pole phases can be changed by the
integer unimodular map used in the original volume. In the resulting actual
$2\pi$-periodic coordinates $(\alpha,\beta)$,

$$
P=\partial_k,
\qquad
Q=\frac12\partial_\alpha+\left(\frac12-\frac{k}{r}\right)\partial_\beta.
\tag{2.1}
$$

The map preserves the full torus and its unnormalized angular measure. It
does not identify a preparation phase with a phase increment. Set
$c(k)=\frac12-k/r$. Then

$$
[P,Q]=-\frac1r\partial_\beta,
\qquad
\operatorname{span}\{P,Q,[P,Q]\}=T\Omega.
\tag{2.2}
$$

Thus the double-wall leaf is a regular contact-type step-two system with
weights $(1,1,2)$ and volume exponent $4$. This is a statement about the
horizontal operator on the actual three-coordinate current-ray cylinder;
it does not select three Euclidean spatial axes and it does not add a third
control.

For a source $o=(k_o,\alpha_o,\beta_o)$, use the local chart

$$
x=k-k_o,\qquad y=2(\alpha-\alpha_o),\qquad
z=-r\bigl(\beta-\beta_o-c(k_o)y\bigr).
\tag{2.3}
$$

In this chart $P=\partial_x$ and $Q=\partial_y+x\partial_z$. The chart is
injective on a sufficiently small neighbourhood of the source. The
inverse chart is denoted by $\Phi_o$. Its coordinate Jacobian is a fixed
nonzero number $J_o$; retaining $J_o$ below
is useful because the source density need not be constant.

## 3. The tangent operator and source normalization

Let $A=\Sigma\Sigma^{\mathsf T}$ be the smooth positive square root on a
neighbourhood of $\overline\Omega$, and put

$$
Y_a=\sum_{i=1}^2\Sigma_{ia}X_i,
\qquad
T_A[f]=\sum_{a=1}^2\|Y_af\|_{L^2(\mu)}^2.
\tag{3.1}
$$

In the chart (2.3), freeze the coefficients and the density at the source:

$$
\widehat X_1=\partial_x,\qquad
\widehat X_2=\partial_y+x\partial_z,\qquad
\widehat Y_a=\sum_{i=1}^2\Sigma_{ia}(o)\widehat X_i,
$$

$$
d\widehat\mu=\rho(o)|J_o|\,dx\,dy\,dz,\qquad
\widehat L_o=-\sum_{a=1}^2\widehat Y_a^2.
\tag{3.2}
$$

The drift caused by the variable density and the variable square root is
horizontal and has homogeneous degree one less than the principal part. It
therefore disappears under the step-two dilation

$$
\delta_s(x,y,z)=(sx,sy,s^2z),\qquad |\det D\delta_s|=s^4.
\tag{3.3}
$$

The frozen fields are an invertible change of the standard Heisenberg
horizontal frame. Put $B=\Sigma(o)^{-1}$ and define the induced graded group
automorphism $F_B$ in the displayed second-kind coordinates by

$$
\binom{\xi}{\eta}=B\binom{x}{y},
\qquad
\zeta=\det(B)\left(z-\frac{xy}{2}\right)+\frac{\xi\eta}{2}.
\tag{3.3a}
$$

Indeed the first-kind central coordinate is $t=z-xy/2$: in
$(x,y,t)$ the map is the linear graded map
$(x,y,t)\mapsto(B(x,y),\det(B)t)$. Formula (3.3a) is its expression back
in second-kind coordinates, including the homogeneous quadratic central
correction. It commutes with $\delta_s$ and has absolute Jacobian
$\det(B)^2$. Its pushforwards satisfy
$(F_B)_*\widehat Y_1=U$ and $(F_B)_*\widehat Y_2=V$, so it carries
$\widehat L_o$ exactly to $-(U^2+V^2)$, where

$$
U=\partial_\xi,\qquad V=\partial_\eta+\xi\partial_\zeta.
$$

Consequently the frozen heat kernel has a positive full Green kernel
$G_o$ satisfying

$$
G_o(\delta_s q)=s^{-2}G_o(q),
\qquad G_o(q)>0\ (q\ne0),
\qquad G_o\in C^\infty(\mathbb R^3\setminus\{0\}).
\tag{3.4}
$$

The normalization in (3.4) is relative to the constant measure
$d\widehat\mu$. With $m_o=\rho(o)|J_o|$, its pushforward is
$m_o\det(B)^{-2}\,d\xi\,d\eta\,d\zeta$. Thus if $G_H$ denotes the
Lebesgue-normalized Green kernel for $-(U^2+V^2)$, then
$G_o(q)=\det(B)^2m_o^{-1}G_H(F_Bq)$. This is the unit source for the same
density convention as (1.2), with no change of coupling.

The homogeneous norm $N_o$ obtained by pulling back a standard Heisenberg
gauge gives constants $0<c_o\le C_o<\infty$ with

$$
c_oN_o(q)^{-2}\le G_o(q)\le C_oN_o(q)^{-2}
\tag{3.5}
$$

on every fixed sufficiently small punctured chart. The upper estimate is
all that is needed for weak coupling; the lower estimate supplies the
large-coupling witnesses.

The exact upper statement used below is for the full Green field. There are
a neighbourhood $U_o$ and finite constants $C_{G,o}>0$, $B_{G,o}\ge0$ such that the
full killed field obeys, for $q\in U_o\setminus\{o\}$,

$$
0\le \Gamma_{A,o}(q)
\le C_{G,o}N_o(q)^{-2}+B_{G,o}.
\tag{3.6}
$$

For every compact annulus $K\Subset\mathbb R^3\setminus\{0\}$ there is a
$c_K>0$ such that, for all sufficiently small $s$,

$$
s^2\Gamma_{A,o}(\Phi_o(\delta_s\xi))\ge c_K
\quad\text{for }\xi\in K.
\tag{3.7}
$$

The lower estimate is obtained from a positive-time slice of the full Green
integral; the field itself remains the integral over all $t\in(0,\infty)$.

**Proposition 3.1 (full killed tangent comparison).** Equations (3.6) and
(3.7) hold for every fixed smooth positive $\rho$, every fixed smooth SPD
$A$, every source in the interior, and the killed cylinder in (1.1).

**Proof.** The rescaled principal fields converge in $C^\infty$ on compact
sets to the frozen fields in (3.2). The rescaled horizontal drift is lower
order. The coefficient and density hypotheses are exactly those required by
the positive-time nilpotentization theorem of Colin de Verdière--Hillairet--
Trélat, Theorem B and (2.8), together with its local comparison theorem.
Jerison--Sánchez-Calle, §6, records the same Gaussian heat bounds for
operators

$$
\sum_jX_j^2+\sum_{i,j}c_{ij}[X_i,X_j]+\sum_jb_jX_j
$$

with smooth real coefficients. Taking $X_j=Y_j$, $c_{ij}=0$, and
$b_j=\operatorname{div}_\mu Y_j$ gives the symmetric generator associated
with (3.1); the coefficients are smooth because $A$ and $\rho$ are smooth
and $A$ is SPD. Thus the heat kernels on the rescaled cylinder converge on
every compact positive-time interval to the frozen heat kernel, with the
normalization $d\widehat\mu$ retained.

For the upper bound, the same local theorem and the Jerison--Sánchez-Calle
Gaussian estimate give, in the chart,

$$
p_t^\Omega(o,\Phi_o(\delta_s\xi))
\le C t^{-2}\exp\!\left(-c\frac{N_o(\delta_s\xi)^2}{t}\right)
$$

for the small-time range, with fixed-model constants. Integrating in $t$
and using the positive killed gap for the tail gives
$\Gamma_{A,o}\le C_{G,o}N_o^{-2}+B_{G,o}$. This is an upper bound for the
full time integral, not a time-window replacement. For the lower bound,
positive smoothness of the frozen heat kernel on $[1,2]\times K$ and the
positive-time nilpotentization theorem give, uniformly on $K$,

$$
s^4p_{s^2\tau}^\Omega(o,\Phi_o(\delta_s\xi))\ge c'_K
\qquad(1\le\tau\le2).
$$

Integrating this displayed slice over $s^2\le t\le2s^2$ yields (3.7).
Dirichlet localization and the semigroup contraction keep the cylinder,
density and source normalization unchanged. No tangent operator replaces
$L_A$ in the definition of $\Gamma_{A,o}$. $\square$

The proposition uses the primary sources only for their stated local heat
and coefficient hypotheses. It does not infer a global Green identity from
positive-time continuity. The long-time part is controlled separately by
the actual killed gap, and the source normalization is fixed by (3.2).

## 4. The unweighted Hardy estimate and localization

Define the frozen energy quantity

$$
\mathscr T_o[v]=\sum_{a=1}^2\int|\widehat Y_av|^2\,d\widehat\mu.
\tag{4.1}
$$

**Proposition 4.2 (relative control by the actual full Green field).** There
are finite constants $K_o>0$ and $B_o\ge0$ such that
$V_{A,o}[f]\le K_oT_A[f]+B_o\|f\|_2^2$ for every $f\in\mathcal F_A$.

**Proof.** The unweighted Hardy supplier is the same
Ciatti--Cowling--Ricci Corollary 3.2 used inside the original volume's
Proposition 4.3. Apply it on the standard Heisenberg group with $p=2$,
$\alpha=1$ and homogeneous dimension $Q=4$; its strict hypothesis is
$0<1<4/2$. For $w\in C_c^\infty(\mathbb R^3)$ it gives

$$
\int N^{-2}|w|^2\,d\xi\,d\eta\,d\zeta
\le C\|(-(U^2+V^2))^{1/2}w\|_2^2
=C\int(|Uw|^2+|Vw|^2)\,d\xi\,d\eta\,d\zeta.
$$

Here $N$ is the homogeneous gauge whose pullback by (3.3a) is $N_o$.
Pulling back this attributed inequality through $F_B$, the constant
Haar-measure multiplier occurs on both sides and cancels. Hence there is a
finite $H_o>0$ with

$$
\int N_o^{-2}|v|^2\,d\widehat\mu\le H_o\mathscr T_o[v]
\qquad(v\in C_c^\infty(\mathbb R^3)).
\tag{4.2}
$$

This is an unweighted inverse-gauge estimate; no factor such as
$|\nabla_HN|^2$ is inserted.

Shrink $U_o$ to a relatively compact chart if necessary. Smooth positivity
and SPD give finite $d_o,a_o\ge1$ such that throughout the chart

$$
d_o^{-1}d\widehat\mu\le\Phi_o^*d\mu\le d_o\,d\widehat\mu,
\qquad
A(o)\le a_o A(\Phi_o(q))
$$

as measures and quadratic forms, respectively. For
$u\in C_c^\infty(U_o)$ and $v=u\circ\Phi_o$, the exact fields
$P,Q$ in (2.3) are $\widehat X_1,\widehat X_2$, so
$\mathscr T_o[v]\le a_od_oT_A[u]$. Therefore

$$
\int_{U_o}N_o^{-2}|u|^2\,d\mu
\le d_oH_o\mathscr T_o[v]
\le a_od_o^2H_oT_A[u].
$$

Fix the nonsharp comparison multiplier and relative coefficient as

$$
M_o:=a_od_o^2,\qquad K_o:=C_{G,o}M_oH_o>0.
$$

This finite factor absorbs both density comparisons and the covariance
comparison. With this choice of $K_o$, the bound to prove is

$$
V_{A,o}[f]\le C_{G,o}M_oH_oT_A[f]+B_o\|f\|_2^2
=K_oT_A[f]+B_o\|f\|_2^2
\qquad(f\in\mathcal F_A).
\tag{4.3}
$$

Choose smooth real cutoffs $\chi,\vartheta$ with
$\chi^2+\vartheta^2=1$, $\chi=1$ near $o$, and $\chi$ supported in $U_o$.
For instance choose $\chi=\cos\theta$, $\vartheta=\sin\theta$, with
$\theta=0$ near $o$ and $\theta=\pi/2$ outside the chart. On the
$\chi$ part, (3.6) and the preceding comparison give the coefficient
$K_o$. The coefficients of
$P\chi,Q\chi,P\vartheta,Q\vartheta$ are bounded, so the horizontal product
rule gives

$$
T_A[\chi f]+T_A[\vartheta f]
\le T_A[f]+C_\chi\|f\|_2^2.
\tag{4.4}
$$

The $B_{G,o}$ term in (3.6) and the complement of the source chart are
bounded by Proposition 2.2 of the original volume. Combining these facts
gives (4.3) on $C_c^\infty(\Omega\setminus\{o\})$.

The punctured core is dense in $\mathcal F_A$: in the step-two chart, a
smooth cutoff equal to one near the source and supported in a dilation of
radius $s$ has squared $L^2$ norm $O(s^4)$ (thus $L^2$ norm $O(s^2)$) and
horizontal energy $O(s^2)$. For each fixed smooth core function,
multiplication by the cutoff's complement therefore converges in the free
form norm; core approximation gives the asserted density.
Applying (4.3) to differences of a core sequence makes
the weighted $L^2(\Gamma_{A,o}d\mu)$ sequence Cauchy. The $L^2$ limit agrees
almost everywhere with the ordinary form limit, and (4.3) therefore passes
to every $f\in\mathcal F_A$. $\square$

The estimate is deliberately fixed-model. Neither $H_o$, $M_o$, $K_o$ nor
$B_o$ is asserted to remain bounded when the density, covariance,
source, interval or means vary.

## 5. Weak coupling on the exact horizontal domain

**Theorem 5.1 (double-wall weak-coupling interval).** In the both-wall row,
set

$$
g_-:=\frac{1}{2K_o}=\frac{1}{2C_{G,o}M_oH_o}>0.
\tag{5.1}
$$

For every $0<g<g_-$, the full form $q_{A,g}$ is closed and semibounded on
exactly $\mathcal F_A$. Its shifted norm is equivalent to the free form
norm, its associated operator has compact resolvent, and its normalized
lowest energy is finite and attained.

**Proof.** Proposition 4.2 gives a relative form bound
$a=gK_o=gC_{G,o}M_oH_o<1/2$ and an additive bound $b=gB_o$. The KLMN
theorem, in the form of Teschl, Theorem 6.24, applies to the closed
nonnegative form $T_A$ and the Hermitian perturbation $-gV_{A,o}$. It yields
closedness and semiboundedness on the unchanged domain $\mathcal F_A$, with

$$
q_{A,g}[f]\ge(1-a)T_A[f]-b\|f\|_2^2.
\tag{5.2}
$$

For a shift $c>b+1$, the norms from $q_{A,g}+c\|\cdot\|_2^2$ and
$T_A+\|\cdot\|_2^2$ dominate each other. The compact embedding
$\mathcal F_A\hookrightarrow L^2(\Omega,\mu)$ from Proposition 2.1 of the
original volume therefore gives compact resolvent for the perturbed form.
Any normalized minimizing sequence is bounded in the shifted form norm and
has a strongly $L^2$-convergent subsequence. Weak lower semicontinuity of
the shifted form preserves the norm constraint and attains the infimum.
The Euler--Lagrange equation places the minimizer in the associated
operator domain. $\square$

The interval is a semiboundedness interval, not a claim that the minimum is
positive. Its sign depends on the fixed source and model. No endpoint is
claimed and no all-model threshold is asserted.

## 6. Finite large-coupling collapse on the same model

Choose a nonzero $v\in C_c^\infty(\mathbb R^3\setminus\{0\})$ supported in
an annulus $K$ from (3.7). Put

$$
E_v:=\mathscr T_o[v],
\qquad
D_v:=c_K\int|v|^2\,d\widehat\mu>0,
\qquad
R_o(v):=\frac{E_v}{D_v}<\infty.
\tag{6.1}
$$

Transport the anisotropically normalized dilation of $v$ through the actual
chart:

$$
f_s(\Phi_o(\delta_s\xi))
 =s^{-2}\nu_{v,s}v(\xi),
\tag{6.2}
$$

where $\nu_{v,s}>0$ is chosen so that $\|f_s\|_{L^2(\mu)}=1$; these
normalizers converge to a positive finite $\nu_v$. For all small $s$,
the support is an actual compact annulus in $\Omega\setminus\{o\}$, so
$f_s\in C_c^\infty(\Omega\setminus\{o\})\subset\mathcal F_A$.

**Theorem 6.1 (finite sufficient collapse bound).** For every fixed
double-wall model and source, there is a finite $g_+(o,A,\rho,I)$ such that

$$
g>g_+\quad\Longrightarrow\quad
\inf_{\substack{f\in\mathcal F_A\\\|f\|_2=1}}q_{A,g}[f]=-\infty.
\tag{6.3}
$$

One admissible choice is $g_+=R_o(v)$ for the annular witness in (6.1);
hence a finite choice exists without taking a
sharp infimum.

**Proof.** The rescaled fields converge to the frozen fields in
$C^\infty$ on the support of $v$, and the rescaled density converges to
$d\widehat\mu$. Therefore

$$
T_A[f_s]=s^{-2}\nu_{v,s}^2\bigl(E_v+o(1)\bigr),
\qquad
\liminf_{s\downarrow0}s^2V_{A,o}[f_s]\ge\nu_v^2D_v.
\tag{6.4}
$$

The second relation is (3.7), which uses the full killed Green field. If
$g>R_o(v)$, choose $\delta>0$ so that $E_v-gD_v<-2\delta$.
Equations (6.4) then give

$$
q_{A,g}[f_s]\le-\delta\nu_v^2s^{-2}
$$

for all sufficiently small $s$. Letting $s\downarrow0$ proves (6.3).
The bound is sufficient, fixed-model and finite. It is neither a sharp
critical coupling nor a statement that every $g>g_+$ has the same ground
state sign on a different model. $\square$

The large-coupling statement and Theorem 5.1 are logically separate. The
small interval follows from an unweighted relative form inequality; the
collapse follows from normalized annular states and the leading full-Green
homogeneity. No equality case is settled.

## 7. The fixed-model iff classification

**Theorem 7.1 (native weak stability iff both walls).** For every fixed
choice of means, interior cylinder, source, smooth positive density and SPD
horizontal covariance in Definition 1.3, the following are equivalent:

1. There is a nonempty interval $(0,g_0)$ such that for every
   $g\in(0,g_0)$ the full killed form $q_{A,g}$ is closed and semibounded on
   exactly $\mathcal F_A$, has equivalent shifted form norms and compact
   resolvent, and its normalized minimum is attained.
2. Both native walls $E_-$ and $E_+$ hold, so the current-ray dimension is
   $3$, the direct rank is $2$, the growth vector is $(2,3)$, and the native
   volume exponent is $4$.

**Proof.** If both walls hold, Theorem 5.1 supplies (1) for the fixed
model. If either wall fails, the original volume's Theorem 3.1 applies to
the same $\rho$, $A$, killed cylinder and full Green field. Its normalized
privileged annular tests satisfy

$$
T_A[f_s]\le Cs^{-2},\qquad
V_{A,o}[f_s]\ge cs^{2-Q_{\rm vol}},
$$

with $Q_{\rm vol}=7$ on a single wall and $Q_{\rm vol}=11$ off both. Since
$Q_{\rm vol}>4$, the negative term dominates for every fixed $g>0$ and
$q_{A,g}[f_s]\to-\infty$. Therefore no positive weak-coupling interval with
the property in (1) exists. The two implications use the same native
operator and source conventions; neither changes the form domain. $\square$

This is an iff for each fixed model. It does not say that a single constant
works uniformly over densities, covariances, intervals or sources. It also
does not select the physical meaning of three dimensions: the dimension in
the theorem is the current-ray coordinate count, while direct stochastic
rank remains two.

## 8. Exact scope and supplier correspondence

The proof reuses the original volume as follows.

| Input | Use here | Boundary retained |
| --- | --- | --- |
| [N, Definitions 2.1, 3.1, 8.1; Theorem 10.3](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md) | Native means, grouped phases, actual torus, two fields, wall table and guards | No preparation, control or physical-space claim is added |
| Original volume, Propositions 2.1--2.2 | Closed free form, positive gap, compact embedding, full killed unit-source Green and $L^1$ tail | Same $\rho$, $A$, clock, source and height killing |
| Original volume, Theorem 3.1 | All-$g$ concentration on the single-wall and neither-wall rows | Its $Q_{\rm vol}=7,11$ tests are reused without relabelling |
| Colin de Verdière--Hillairet--Trélat, Theorem B, (2.8), and Theorem 3.2 | Positive-time nilpotentization, local comparison and smooth-density realization | No global Green limit is inferred from this supplier alone |
| Jerison--Sánchez-Calle, §6, printed p.853 | Gaussian bounds for smooth Hörmander operators with horizontal lower-order terms | The target drift is exactly $\sum_j(\operatorname{div}_\mu Y_j)Y_j$ |
| Ciatti--Cowling--Ricci, Corollary 3.2 | Unweighted inverse-gauge Hardy estimate with $p=2$, $\alpha=1$, $Q=4$ | No gradient-weighted potential is substituted |
| Teschl, Theorem 6.24 | KLMN closure on the original form domain | Compactness and attainment are proved separately |

The native phase torus is never replaced by a quotient, phase average or
noncompact cover. The source is the same point source used in Definition
1.3, and every large-coupling witness is normalized in the entire original
horizontal form domain. The argument establishes no negative minimum for
arbitrary coefficients at identity covariance, no sharp endpoint, no equal
operator domains, and no uniform threshold over all fixed models. It also
does not add an empirical realization, a Euclidean-three selection, or a
new noise-control direction.

The genuine extension relative to the original volume is the fixed-model
coefficient-and-density tangent comparison (3.6)--(3.7), its unweighted
relative form estimate (4.3), and the resulting iff plus finite obstruction
(5.1), (6.3), and (7.1). The earlier constant-density diagonal family is a
special case and is not used as a substitute for this variable-coefficient
argument.

## 9. Remaining boundaries

The finite numbers $H_o$, $M_o$, $K_o$, $g_-$ and $g_+$ depend on the fixed source,
density, covariance, interval and local chart. Optimizing them, deciding the
critical equality case, or comparing them across models is outside this
unit. The result concerns the original killed cylinder and its actual full
Green field only; removing killing, changing the clock, decompactifying a
phase, or replacing the horizontal closure by an isotropic Sobolev domain
would be a different theorem.

## 追加锚（本行以下为增补区）

## 10. Unit-source normalization and the operative tangent constant

**Definition 10.1 (source coordinates and angular boundary problem).**
Assume both native walls and retain all the data of (1.1)--(1.2), including
unnormalized phase measure. In (2.3) the absolute inverse Jacobian is
$|J_o|=1/(2r)$. Put $\Sigma_o=A(o)^{1/2}$ and $B=\Sigma_o^{-1}$.
First pass to $t=z-xy/2$, then set

$$
(\xi,\eta)^{\mathsf T}=B(x,y)^{\mathsf T},\qquad
\tau=\det(B)t.
\tag{10.1}
$$

Write $\Psi$ for this source-centred chart. Its horizontal frame and
measure have the exact expressions

$$
\begin{aligned}
U&=\partial_\xi-\tfrac\eta2\partial_\tau,
&V&=\partial_\eta+\tfrac\xi2\partial_\tau,\\
d\mu&=m(q)\,dq,
&m(q)&=\frac{\det A(o)}{2r}\rho(\Psi^{-1}q),\\
C(q)&=BA(\Psi^{-1}q)B^{\mathsf T},
&m_0=m(0)&=\frac{\rho(o)\det A(o)}{2r}.
\end{aligned}
\tag{10.2}
$$

Here $dq=d\xi\,d\eta\,d\tau$, $C(0)=I_2$, and the energy in the chart
is $\int m\langle C\nabla_H f,\nabla_H f\rangle dq$, with
$\nabla_H=(U,V)$. The chart is used only on an injective neighbourhood;
no covering or identification of actual phases is made. Define

$$
R=\big((\xi^2+\eta^2)^2+16\tau^2\big)^{1/4},\qquad
J=(-\pi/2,\pi/2),\qquad c(a)=\cos a.
\tag{10.3}
$$

The angular operator $S$ is the operator of the closed form

$$
\int_J\{4c|b'|^2+c|b|^2\}\,da
\quad\hbox{on}\quad
\mathcal H_c=\{b\in L^2(J):b\in AC_{\rm loc}(J),\quad
\sqrt c\,b'\in L^2(J)\}.
\tag{10.4}
$$

Thus $Sb=-4(cb')'+cb$ with natural endpoint conditions, not Dirichlet
conditions. Denote its lowest eigenvalue by $\lambda_0$ and its positive
eigenfunction by $\phi$, normalized by $\phi(0)=1$. Equivalently,
$\lambda_0$ is the unique parameter for which the solution

$$
-4(c\phi')'+c\phi=\lambda_0\phi,\qquad
\phi(0)=1,\quad\phi'(0)=0
\tag{10.5}
$$

is positive and regular at both endpoints. Regularity means the bounded
branch, with $c\phi'\to0$ at each endpoint. In particular it can be
specified by a scalar shooting condition: let $\phi_\lambda$ solve

$$
\phi_\lambda(a)=1+\frac14\int_0^a\frac1{c(s)}
 \int_0^s(c(t)-\lambda)\phi_\lambda(t)dt\,ds,
\qquad 0\le a<\pi/2.
\tag{10.5a}
$$

Then $\lambda_0$ is the unique parameter for which $\phi_\lambda$ stays
positive on $[0,\pi/2)$ and
$\int_0^{\pi/2}(c-\lambda)\phi_\lambda da=0$. This zero-flux condition
selects the regular branch; even reflection supplies the other endpoint.
The constant to be used for the original source is

$$
g_{\mathrm c}=2\pi m_0\lambda_0
=\frac{\pi\rho(o)\det A(o)}{r}\lambda_0.
\tag{10.6}
$$

**Theorem 10.2 (the native tangent normalization, all modes and sharpness).**
The boundary problem (10.5) is operative: $\lambda_0$ is simple,
$0<\lambda_0<2/\pi$, and $\phi$ extends smoothly and positively to
$\overline J$. The unit-source frozen Green kernel of (3.4), in the
original density convention and expressed in coordinates (10.1), is exactly

$$
\widehat\Gamma_o(q)=\frac{1}{2\pi m_0}R(q)^{-2}.
\tag{10.7}
$$

For every complex $u\in C_c^\infty(\mathbb R^3\setminus\{0\})$,

$$
\int |\nabla_Hu|^2dq\ge
\lambda_0\int R^{-2}|u|^2dq,
\tag{10.8}
$$

and $\lambda_0$ is optimal on this full complex test class. In particular,
(10.6) is the optimal frozen coupling for the unit source (10.7), including
all angular and radial Fourier modes. If the angular operator is instead
written $-(cb')'+cb/4$, its eigenvalue is $\lambda_0/4$; the coupling in
(10.6) is unchanged by that change of notation.

**Proof.** The inverse Jacobian of (2.3) is $1/(2r)$ in absolute value.
The graded automorphism (10.1) has determinant $\det(B)^2=1/\det A(o)$;
the first-kind central coordinate change has determinant one. Pushing
forward the original frame gives the coefficient matrix $C$ in (10.2).
This proves both the exact energy correspondence and the density factor
$m_0$, without normalizing either native phase circle.

The classical Heisenberg fundamental solution is the intermediate
supplier here; its particular normalization can also be checked directly.
Set $\Delta_H=U^2+V^2$. Direct differentiation gives
$\Delta_HR^{-2}=0$ away from zero. Use the polar coordinates

$$
\xi=R\sqrt{\cos a}\cos\theta,\qquad
\eta=R\sqrt{\cos a}\sin\theta,\qquad
4\tau=R^2\sin a,
\quad a\in J,\quad\theta\in\mathbb R/(2\pi\mathbb Z).
\tag{10.9}
$$

Their volume element is $R^3dR\,da\,d\theta/4$ and
$|\nabla_HR|^2=\cos a$. The outward flux of $-\nabla_HR^{-2}$ through
$R=\varepsilon$ is therefore
$2\varepsilon^{-3}(\varepsilon^3/4)\int_J\int_0^{2\pi}c\,d\theta da
=2\pi$. Consequently
$-\Delta_H((2\pi)^{-1}R^{-2})=\delta_0$ relative to Lebesgue measure.
The full heat-integral kernel is also homogeneous of degree $-2$ and has
the same distributional source. Its difference from this kernel is globally
$\Delta_H$-harmonic, hence smooth by hypoellipticity. A smooth function
homogeneous of degree $-2$ must be zero. A unit source relative to $m_0dq$
then divides the kernel by $m_0$, proving (10.7). This also identifies the
positive fundamental solution with the full heat-integral kernel
in Ciatti--Cowling--Ricci, §2, equations (2.1), (2.6)--(2.7), with
$Q=4$ and $L=-\Delta_H$; their general result is not an assertion of the
sharp constant in (10.8).

The embedding $\mathcal H_c\hookrightarrow L^2(J)$ is compact. Near an
endpoint put $d=\pi/2-|a|$ and $s=\sqrt d$. The derivative and norm
integrals in (10.4) are comparable to the radial $H^1$ and $L^2$ integrals
on a two-dimensional disk, respectively. Rellich compactness on that disk,
and ordinary one-dimensional compactness in the middle, give the claim.
The form is positive definite; compactness rules out a zero lowest
eigenvalue. Taking a nonnegative lowest eigenfunction, the interior
Sturm equation makes it strictly positive and the lowest eigenvalue
simple. Since $c$ has a simple zero at each endpoint, its regular-singular
ODE has one smooth branch and one logarithmic branch. The latter has
infinite $\int c|b'|^2$. Thus the eigenfunction is the smooth branch.
The endpoint expansion is
$\phi(\pi/2-d)=\phi(\pi/2)(1-\lambda_0d/4+O(d^2))$ and the analogous
expansion at the other end. A zero endpoint value forces the regular
solution to vanish identically. Hence $\min_{\overline J}\phi>0$.
Reflection symmetry and simplicity give evenness and (10.5).
The constant trial has quotient $2/\pi$. Equality in this trial bound
would make that constant an eigenfunction, whereas $S1=c$ is not constant.
This proves the strict upper bound. These observations also give the
stated positive-solution characterization of $\lambda_0$. Integrating
the ODE twice from zero gives (10.5a), and the final integral there is
four times the endpoint flux $\lim_{a\uparrow\pi/2}c(a)\phi_\lambda'(a)$.

For completeness, the passage from this angular problem to the entire
unweighted test class is explicit. Put $\ell=\log R$ and
$u=R^{-1}v(\ell,a,\theta)$. The two horizontal squared derivatives,
including their cross terms, give

$$
\begin{aligned}
\int|\nabla_Hu|^2dq
&=\frac14\int_{\mathbb R\times J\times\mathbb T}
\left\{c|v_\ell-v+\tan a\,v_\theta|^2
+4c|v_a+\tfrac12v_\theta|^2\right\}
\,d\ell\,da\,d\theta,\\
\int R^{-2}|u|^2dq
&=\frac14\int|v|^2\,d\ell\,da\,d\theta.
\end{aligned}
\tag{10.10}
$$

Fourier transformation in $\ell$ and Fourier series in $\theta$, followed
in the $(\sigma,n)$ fibre by the phase $e^{-ina/2}$, give the angular
energy

$$
\int_J\left\{4c|b'|^2+
 c\big(1+(\sigma+n\tan a)^2\big)|b|^2\right\}\,da,
\qquad \sigma\in\mathbb R,\ n\in\mathbb Z.
\tag{10.11}
$$

The extra term is nonnegative. Each admissible fibre belongs to the base
form domain (10.4), so (10.11) is at least
$\lambda_0\int_J|b|^2$. Plancherel proves (10.8). The coordinate axes
omitted by (10.9) have measure zero; the identity for smooth tests follows
by integration over the full polar coordinate region, and then by form
approximation. It imposes no symmetry on $u$.

For actual sharpness let $\chi\in C_c^\infty(\mathbb R)$ be nonzero and
real, and put

$$
u_L(q)=R^{-1}\phi(a)\chi(\log R/L),\qquad L>0.
\tag{10.12}
$$

These are smooth compact annular tests on the entire punctured group.
Smoothness on the central axis follows from the smooth endpoint branch:
$\pi/2-|a|$ is a smooth function of $\xi^2+\eta^2$ there, with
$\tau\ne0$. Formula (10.10) and the angular eigenvalue equation give

$$
\frac{\int|\nabla_Hu_L|^2dq}
 {\int R^{-2}|u_L|^2dq}
=\lambda_0+
\frac{\int_Jc\phi^2da}{\int_J\phi^2da}
\frac{\int_{\mathbb R}|\chi'|^2d\ell}
 {L^2\int_{\mathbb R}|\chi|^2d\ell}.
\tag{10.13}
$$

Thus the lower bound is sharp through actual annular tests. Multiplying
energy by $m_0$ and using (10.7) gives exactly (10.6).
As an attributed quantitative check, D'Arca--Fanelli--Franceschi--Prandi,
[arXiv:2603.04086v1](https://arxiv.org/html/2603.04086v1), Theorem 1.2(1),
with $n=1$, $Q=4$, $p=2$, $\theta=1$, gives $\lambda_0\ge1/4$.
Their central coordinate is $-4\tau$ and their Korányi
norm is (10.3); the constant measure multiplier cancels in the quotient.
That paper supplies a lower bound, not the sharp characterization or the
native critical-domain conclusion proved here. $\square$

## 11. An endpoint-strength comparison with the full killed Green field

**Theorem 11.1 (quantitative full-Green singular part).** For every fixed
smooth positive $\rho$ and smooth SPD $A$ in the original both-wall model,
there are
a chart radius $b_0>0$ and a finite $K$ such that

$$
\left|\Gamma_{A,o}(\Psi^{-1}q)
 -\frac{R(q)^{-2}}{2\pi m_0}\right|
\le K R(q)^{-1},\qquad 0<R(q)<b_0.
\tag{11.1}
$$

In particular the leading coefficient is exact and uses the full
unit-source killed field with its original clock. The comparison is
uniform on every compact rescaled annulus. It includes the entire
small-time and large-time contributions.

**Proof.** All estimates in this proof concern the original free operator.
Chart points in this proof are identified with their native images under
$\Psi^{-1}$. In the chart the differential expression is

$$
L_A=-m^{-1}\sum_{i,j=1}^2 Z_i(mC^{ij}Z_j),\qquad (Z_1,Z_2)=(U,V).
\tag{11.2}
$$

For $R< b_0$ smoothness gives

$$
|C-I|+|m/m_0-1|\le K_1R,\qquad
|\nabla_H C|+|\nabla_H\log m|\le K_1.
\tag{11.3}
$$

The first estimate uses $|\xi|+|\eta|=O(R)$ and $|\tau|=O(R^2)$.
The horizontal distance is locally comparable to the frozen Heisenberg
distance: the horizontal distribution is exactly the same and the two
horizontal metrics are uniformly comparable. After shrinking the chart,
short paths stay in a larger injective chart. Local ball volumes are
comparable to the fourth power of their radius, uniformly on a compact
neighbourhood of the source.

The Gaussian upper estimate of Jerison--Sánchez-Calle, including the
smooth horizontal drift allowed in §6, therefore yields, for $p,q$ in
that neighbourhood and $0<t<t_0$,

$$
p_t^\Omega(p,q)\le K_2t^{-2}
 \exp(-d_H(p,q)^2/(K_2t)).
\tag{11.4}
$$

Here the target drift is exactly
$\sum_j(\operatorname{div}_\mu Y_j)Y_j$ for the smooth square-root frame
(3.1). Dirichlet localization applies to this same expression and density,
as in Colin de Verdière--Hillairet--Trélat, Theorem 3.2. For $t\ge t_0$,
the semigroup identity, the actual positive killed gap, and bounded
positive-time diagonals on this compact neighbourhood give
$ p_t^\Omega(p,q)\le K_3e^{-\lambda_A(t-t_0)}$.
Consequently its full two-point Green kernel satisfies

$$
0\le G_\Omega(p,q):=\int_0^\infty p_t^\Omega(p,q)dt
\le K_4d_H(p,q)^{-2}+K_4.
\tag{11.5}
$$

The bounded term in (11.5) contains the complete large-time tail. No
positive-time tangent limit is being integrated without a tail bound.
The local heat hypotheses, density realization and nilpotent fields are
also exactly those of Colin de Verdière--Hillairet--Trélat, Theorem B,
(2.8), with horizontal drift and step two. Their theorem is consistent
with (11.4), but its order-zero convergence alone is not used to assert
(11.1).

Here is a direct residual argument giving the stronger error needed at
equality. Choose a smooth cutoff $\zeta$ supported in the chart and equal
to one near zero, and write $G_0=(2\pi m_0)^{-1}R^{-2}$. In distributions
relative to $d\mu$,

$$
L_A(\zeta G_0)=\delta_o+F,\qquad
|F(q)|\le K_5 R(q)^{-3}\quad\hbox{near }0,
\tag{11.6}
$$

where $F$ is smooth off zero and compactly supported in the chart.
Indeed $|\nabla_HG_0|=O(R^{-3})$,
$|\nabla_H^2G_0|=O(R^{-4})$, and (11.3) makes the difference from the
frozen expression $O(R^{-3})$. The delta coefficient is one: the frozen
flux in the measure $m_0dq$ is one by (10.7), and the error in that flux
is $O(R)$ on $R=\varepsilon$. The locally integrable residual in (11.6)
therefore has no additional point mass.

The exact resolvent identity is

$$
\Gamma_{A,o}(q)=\zeta(q)G_0(q)
 -\int_\Omega G_\Omega(q,p)F(p)d\mu(p).
\tag{11.7}
$$

One can justify it without assuming that $G_0$ belongs to the free form
domain. For $\psi\in C_c^\infty(\Omega)$, put $u=L_A^{-1}\psi$.
It is smooth on the support of $\zeta$ and bounded; boundedness follows
from short-time $L^\infty$ contraction and the positive-time diagonal/gap
tail. Test (11.6) against $u$, using a cutoff equal to one on the support
of $\zeta$. Its left side is $\int\zeta G_0\psi d\mu$ and its right side
is $u(o)+\int Fu\,d\mu$. The heat-resolvent representation of $u$ and
absolute Fubini, since $F\in L^1$ and the resolvent of $|\psi|$ is
bounded, give (11.7) in distributions. The integral is a distributional solution with right side $F$ and is
smooth off the source by local hypoellipticity. Thus (11.7) holds there
pointwise, with the continuous kernel-integral representative.

For $s=R(q)$, split the integral in (11.7) into
$R(p)<\kappa s$, $R(p)\asymp s$, and $R(p)>K_6s$, with fixed constants
chosen from the triangle inequalities for a homogeneous distance.
In the first region $d_H(p,q)\asymp s$, and
$\int_{R(p)<\kappa s}R(p)^{-3}dp=O(s)$, giving $O(s^{-1})$.
In the middle region $R(p)^{-3}=O(s^{-3})$ and
$\int_{d_H(p,q)<K_7s}d_H(p,q)^{-2}dp=O(s^2)$, again giving
$O(s^{-1})$. In the third region $d_H(p,q)\asymp R(p)$ and the radial
integral is bounded by a constant times
$\int_{K_6s}^{b_0}R^{-2}dR=O(s^{-1})$.
The bounded kernel term and the smooth cutoff annulus contribute $O(1)$.
Density is comparable to Lebesgue measure throughout these estimates.
Combining them with (11.7) proves (11.1). $\square$

## 12. The critical form and its precise completion

**Definition 12.1 (critical ground transform on the original cylinder).**
Put

$$
h(q)=R(q)^{-1}\phi(a(q)).
\tag{12.1}
$$

It is smooth and positive on the punctured chart, including its central
axis. Choose a positive smooth $H$ on $\Omega\setminus\{o\}$ which equals
$h\circ\Psi$ on a smaller chart and equals one outside a larger chart.
A smooth convex interpolation gives such an $H$, bounded below by a
positive constant. Define

$$
\begin{aligned}
d\nu&=H^2d\mu,\\
\mathcal E_H[v]&=\int H^2\sum_{i,j}a^{ij}(X_jv)\overline{X_iv}\,d\mu,\\
\mathcal W_H&=\overline{C_c^\infty(\Omega\setminus\{o\})}
 ^{(\|\cdot\|_{L^2(\nu)}^2+\mathcal E_H)^{1/2}},\\
W&=H^{-1}L_AH-g_{\mathrm c}\Gamma_{A,o}.
\end{aligned}
\tag{12.2}
$$

$L_AH$ in this display is the differential expression off the source.
The measure $\nu$ is finite near the source, since $H^2\asymp R^{-2}$.
All functions and closures in (12.2) live on the actual periodic cylinder;
the outer height killing is encoded by the same compact-core condition.
These objects describe the closure of the original critical form; they
do not change the source, the kinetic operator, or its original domain
$\mathcal F_A$.

**Theorem 12.2 (critical semiboundedness, closability and strict domain
extension).** For every fixed smooth both-wall model under consideration,
$q_{A,g_{\mathrm c}}$ is semibounded and closable on exactly its original
domain $\mathcal F_A$. It is not closed on that domain. Its closure has

$$
\begin{aligned}
D(\overline q_{\mathrm c})&=H\mathcal W_H,\\
\overline q_{\mathrm c}[Hv]&=\mathcal E_H[v]
 +\int W|Hv|^2d\mu,\qquad v\in\mathcal W_H,\\
\mathcal F_A&\subsetneq H\mathcal W_H.
\end{aligned}
\tag{12.3}
$$

The potential in the second line is absolutely form bounded, with
arbitrarily small relative bound, with respect to $\mathcal E_H$.
The completion in (12.3) is compactly embedded in $L^2(\mu)$.
In particular its associated operator has compact resolvent. This last
operator is associated with the completed critical form, not with a
closed form on $\mathcal F_A$.

**Proof.** The angular equation gives

$$
(-\Delta_H-\lambda_0R^{-2})h=0.
\tag{12.4}
$$

The homogeneous smooth function $h$ obeys
$|\nabla_Hh|\le Kh/R$ and $|\nabla_H^2h|\le Kh/R^2$.
Using (11.2)--(11.3), (11.1) and
$g_{\mathrm c}/(2\pi m_0)=\lambda_0$, we obtain

$$
|W|\le K/R\quad\hbox{near the source},
\qquad W\hbox{ bounded outside each source neighbourhood}.
\tag{12.5}
$$

For a complex punctured-core function $f=Hv$, integration by parts gives
the exact identity

$$
q_{A,g_{\mathrm c}}[f]=\mathcal E_H[v]+\int W|f|^2d\mu.
\tag{12.6}
$$

We supply the estimate that makes (12.5) sufficient even at equality.
In the frozen chart let

$$
\mathcal E_0[v]=\int h^2|\nabla_Hv|^2dq.
$$

For $v$ compactly supported in $0<R<b$, $b$ sufficiently small, the
following two inequalities hold with a constant independent of $b,v$:

$$
\int R^{-1}h^2|v|^2dq\le Kb\,\mathcal E_0[v],
\qquad
\int h^2|v|^2dq\le Kb^2\,\mathcal E_0[v].
\tag{12.7}
$$

To prove them for all complex states, use (10.9) and $\ell=\log R$.
Directly, or by the ground identity for (12.4),

$$
\mathcal E_0[v]=\frac14\int\phi^2
 \{c|v_\ell+\tan a\,v_\theta|^2
   +4c|v_a+\tfrac12v_\theta|^2\}\,d\ell da d\theta.
\tag{12.8}
$$

Put $F(\ell,a)=(\int_0^{2\pi}|v|^2d\theta)^{1/2}$.
The real part of $\int v_\theta\overline v\,d\theta$ is zero.
Cauchy--Schwarz therefore bounds the right side of (12.8) below by

$$
\frac14\int\phi^2\{c|F_\ell|^2+4c|F_a|^2\}\,d\ell da.
\tag{12.9}
$$

Regularizing the square root handles zeros of $F$. This estimate is for
the norm of the entire angular function, not a restriction to its zeroth
mode. On $J$ the elementary weighted inequality

$$
\int_J\phi^2F^2da\le K
 \int_J c\phi^2(F^2+|F_a|^2)da
\tag{12.10}
$$

follows by joining each point to a fixed middle interval. Cauchy--Schwarz
uses $\int c^{-1}da=O(1+|\log d|)$ up to endpoint distance $d$;
$\int_0^{d_0}|\log d|dd$ is finite. The middle-interval term is bounded
by $\int cF^2$, and the bounded positive factors $\phi^2$ are harmless.

For $p=1,2$, any compactly supported function of
$\ell<\log b$ satisfies, by integration by parts and Cauchy--Schwarz,

$$
\int e^{p\ell}F^2d\ell
\le\frac{4b^p}{p^2}\int|F_\ell|^2d\ell.
\tag{12.11}
$$

Indeed $p\int e^{p\ell}F^2=-2\int e^{p\ell}FF_\ell$ and
$e^{2p\ell}\le b^pe^{p\ell}$.
Multiply (12.10) by $e^{p\ell}$, use (12.11) on its $cF^2$ term,
and bound its derivative term by $b^p\int c\phi^2|F_a|^2$.
The cases $p=1,2$ are exactly (12.7), by (12.9).

The actual $m,C$ are uniformly comparable to $m_0,I_2$ on this chart,
so the same estimates hold for $\mathcal E_H$ and $d\mu$ there, with
fixed-model constants. Localize with a cutoff equal to one on $R<b$ and
supported in $R<2b$, whose horizontal gradient is $O(b^{-1})$.
The product rule and (12.7), together with $R^{-1}\le b^{-1}$ off the
smaller ball, give, for every $\varepsilon>0$,

$$
\int |W|H^2|v|^2d\mu
\le\varepsilon\mathcal E_H[v]
   +K_\varepsilon\|v\|_{L^2(\nu)}^2.
\tag{12.12}
$$

The constants may depend on the entire fixed model. No uniformity over
$A,\rho,I,o$ is used.

The weighted kinetic form is closable: if $v_n\to0$ in $L^2(\nu)$ and
its horizontal derivatives are Cauchy, testing on compact sets avoiding
$o$, where the weight is smooth and positive, makes every derivative
limit zero. The source has measure zero. Its closure is the form with
domain $\mathcal W_H$ in (12.2). The usual KLMN theorem, here used as the
literature-attested intermediate result in Teschl, Theorem 6.24, applies
to (12.12) with relative bound less than one. It makes the right side of
(12.3) a closed semibounded form with norm equivalent to
$\mathcal E_H+\|\cdot\|_{L^2(\nu)}^2$. Multiplication by $H$ is an isometry
from $L^2(\nu)$ to $L^2(\mu)$. By (12.6) this is the closure of the
punctured-core critical form.

The punctured core is dense in $\mathcal F_A$ by Proposition 4.2, and
$V_{A,o}$ is finite and free-form continuous there by (4.3).
Thus the original critical form is the restriction of this closure to
$\mathcal F_A$, and itself has the same closure. For clarity, a free-core
approximation is Cauchy in the shifted critical norm, because (12.6) gives
semiboundedness and $q_{A,g_{\mathrm c}}\le T_A$. This proves the claimed
inclusion and closability without asserting completeness of
$\mathcal F_A$ in that weaker norm.

The inclusion is strict in every such model. Choose a smooth cutoff
$\chi_0$ supported where $H=h\circ\Psi$ and equal to one near $o$.
Take radial logarithmic cutoffs $\eta_\epsilon$ that are zero for
$R\le\epsilon^2$ and one for $R\ge\epsilon$, smoothed so that
$|\partial_R\eta_\epsilon|\le K/(R|\log\epsilon|)$.
Then

$$
\mathcal E_H[\chi_0(1-\eta_\epsilon)]\longrightarrow0,
\qquad
\|\chi_0(1-\eta_\epsilon)\|_{L^2(\nu)}\longrightarrow0.
\tag{12.13}
$$

The derivative integral is $O(|\log\epsilon|^{-1})$; the norm integral
is $O(\epsilon^2)$. These integral estimates make $\chi_0\eta_\epsilon$
a Cauchy family in the weighted form norm, with $L^2(\nu)$ limit
$\chi_0$. Consequently $\chi_0H\in H\mathcal W_H$.
It does not belong to $\mathcal F_A$: its frozen horizontal energy near
zero is a positive constant times $\int_0^b dR/R=\infty$, and the actual
energy is comparable to that energy. Equivalently,
$\int R^{-2}|\chi_0H|^2d\mu=\infty$, contrary to the unweighted Hardy
bound valid on $\mathcal F_A$. The approximants
$\chi_0H\eta_\epsilon$ belong to the original punctured core and converge
in the completed critical norm, so $q_{A,g_{\mathrm c}}$ on
$\mathcal F_A$ is not closed. For the added element the separate kinetic
and Green integrals are both infinite. Its completed form value is the
finite value in (12.3), not an assigned value to an undefined subtraction
of two infinities.

Finally a bounded set in the completed form norm has uniformly small
$L^2(\mu)$ mass near the source. In fact (12.12), or its identical proof
with $|W|$ replaced by $R^{-1}$ near $o$, gives
$\int_{R<d}|f|^2d\mu\le Kd(\mathcal E_H[f/H]+\|f\|_2^2)$.
Away from this ball a cutoff of $f$ is bounded in the original free form
norm: $H,H^{-1}$ and its horizontal derivatives are bounded there.
The compact embedding of the original free domain, already supplied by
the original volume's Proposition 2.1, gives compactness of each such
cutoff. Combining it with the uniform vanishing of the source mass proves
compactness of the completed domain. $\square$

## 13. Sharp original-domain classification and the critical minimum

**Theorem 13.1 (the sharp full-Green coupling for every smooth native
model).** Retain the entire original both-wall model and (10.6). Then:

1. For $0<g<g_{\mathrm c}$, $q_{A,g}$ is closed and semibounded on exactly
   $\mathcal F_A$. Its sufficiently shifted norm is equivalent to the
   original free form norm; its represented operator has compact resolvent;
   and its normalized lowest energy is finite and attained in that domain.
2. For $g>g_{\mathrm c}$, normalized members of the original punctured
   core have energies tending to $-\infty$.
3. At $g=g_{\mathrm c}$ the original form is semibounded and closable,
   but not closed and not norm equivalent to the free form on
   $\mathcal F_A$. Its finite normalized infimum equals the lowest energy
   of (12.3), but is not attained by any member of $\mathcal F_A$.
   The completed form does attain it. Every nonnegative completed ground
   state $f$ satisfies, on a sufficiently small source neighbourhood,

$$
0<d_f h(q)\le f(\Psi^{-1}q)\le D_f h(q),
\qquad 0<R(q)<b_f,
\tag{13.1}
$$

   for finite $d_f,D_f>0$. In particular every such state is outside
   $\mathcal F_A$.

The optimal boundary is therefore $g_{\mathrm c}$ for global
semiboundedness, with equality included, and also the supremum of the
strict closed-form range on the original domain, with equality excluded.
These are two different endpoint assertions.

**Proof.** Theorem 12.2 gives a finite $B$ such that

$$
q_{A,g_{\mathrm c}}[f]\ge-B\|f\|_2^2,
\qquad
V_{A,o}[f]\le g_{\mathrm c}^{-1}T_A[f]
 +(B/g_{\mathrm c})\|f\|_2^2
\quad(f\in\mathcal F_A).
\tag{13.2}
$$

For $g<g_{\mathrm c}$ the relative bound is $g/g_{\mathrm c}<1$.
KLMN applies on exactly $\mathcal F_A$, and directly

$$
q_{A,g}[f]\ge(1-g/g_{\mathrm c})T_A[f]
 -(g/g_{\mathrm c})B\|f\|_2^2,
\qquad q_{A,g}[f]\le T_A[f].
\tag{13.3}
$$

These inequalities prove shifted norm equivalence. Compactness and
attainment follow from the original free compact embedding and weak
lower semicontinuity, as in the proof of Theorem 5.1. They do not require
positivity of the attained energy.

For $g>g_{\mathrm c}$ choose one finite $L$ in (10.12)--(10.13) so that

$$
m_0\int|\nabla_Hu_L|^2dq
 -\frac{g}{2\pi}\int R^{-2}|u_L|^2dq<0.
\tag{13.4}
$$

Use this single compact annular function $v=u_L$ in the actual chart:
$f_s(\Psi^{-1}(\delta_s q))=s^{-2}a_sv(q)$, with $a_s>0$ chosen for
unit $L^2(\mu)$ norm. Then
$a_s\to(m_0\int|v|^2dq)^{-1/2}$, and exact field homogeneity, smooth
coefficients and (11.1) give

$$
\begin{aligned}
T_A[f_s]&=a_s^2s^{-2}
 \left(m_0\int|\nabla_Hv|^2dq+O(s)\right),\\
V_{A,o}[f_s]&=a_s^2s^{-2}
 \left(\frac1{2\pi}\int R^{-2}|v|^2dq+O(s)\right).
\end{aligned}
\tag{13.5}
$$

All error estimates are uniform on this fixed annulus. Its small dilates
lie inside an injective chart of the actual torus cylinder; hence
$f_s\in C_c^\infty(\Omega\setminus\{o\})$ for small $s$. Equations
(13.4)--(13.5) prove normalized collapse. They also show why the exact
source density, rather than a normalized or averaged density, occurs in
the sharp boundary.

It remains to prove the critical attainment assertion, which does not
follow just from nonclosedness. The completed critical form is
semibounded with compact domain embedding by Theorem 12.2. The direct
method therefore gives a normalized completed minimizer of energy $E$.
Taking its absolute value cannot increase (12.3), so there is a
nonnegative minimizer. It solves

$$
(L_A-g_{\mathrm c}\Gamma_{A,o})f=Ef
\quad\hbox{on }\Omega\setminus\{o\}.
\tag{13.6}
$$

Local hypoellipticity makes it smooth there. It is strictly positive.
For example choose $C\ge\max(0,-E)$; then
$(L_A+C)f=(g_{\mathrm c}\Gamma_{A,o}+E+C)f\ge0$ off the source.
On any relatively compact connected subdomain avoiding $o$, comparison
with its positive killed heat semigroup makes a nonzero nonnegative
supersolution strictly positive. Propagation through overlapping
subdomains gives positivity on the connected punctured cylinder. This
uses the same smooth Hörmander positivity as the original free heat
input, only on sets where the attractive coefficient is smooth.

Here is a local barrier argument sufficient for the lower and upper
bounds in (13.1), without importing a singular-endpoint regularity or
attainment theorem. Write

$$
\overline c=\frac{\int_Jc\phi^2da}{\int_J\phi^2da}>0,
\qquad
\mathcal A b=-\frac4{\phi^2}(c\phi^2b')'.
\tag{13.7}
$$

There is a smooth real bounded $w$ on $\overline J$ satisfying
$\mathcal Aw=c-\overline c$, with bounded derivatives and zero endpoint
flux. Indeed define

$$
c(a)\phi(a)^2w'(a)
=-\frac14\int_{-\pi/2}^{a}\phi(s)^2(c(s)-\overline c)ds
\tag{13.8}
$$

and fix its additive constant arbitrarily. The numerator vanishes at
both endpoints and to first order there, so division by the simple zero
of $c$ leaves a smooth derivative. Choose $0<\delta<1$ sufficiently
small that $b_\delta=1+\delta^2w$ is positive and
$\delta^2|cw|\le\overline c/2$. Put

$$
k_\delta=R^{-1+\delta}\phi(a)b_\delta(a)>0.
\tag{13.9}
$$

For a $\theta$-independent homogeneous function $R^p b(a)$,
$\Delta_H(R^pb)=R^{p-2}\{p(p+2)cb+4(cb')'\}$.
Using (13.7)--(13.8) therefore gives the uniform strict sign

$$
\begin{aligned}
(-\Delta_H-\lambda_0R^{-2})k_\delta
&=R^{-3+\delta}\phi
  (\mathcal A-\delta^2c)b_\delta\\
&=R^{-3+\delta}\phi
 (-\delta^2\overline c-\delta^4cw)\\
&\le-\tfrac12\delta^2\overline c\,
 R^{-3+\delta}\phi.
\end{aligned}
\tag{13.10}
$$

Let $\mathcal P_E=L_A-g_{\mathrm c}\Gamma_{A,o}-E$, in the chart.
Equations (11.1)--(11.3) and homogeneity imply

$$
\mathcal P_Eh=O(R^{-2}),\qquad
\mathcal P_Ek_\delta
=(-\Delta_H-\lambda_0R^{-2})k_\delta+O(R^{-2+\delta}).
\tag{13.11}
$$

Since $\delta<1$, the negative term in (13.10) dominates both errors
near zero. Thus, after reducing $b$,

$$
\mathcal P_E(h+k_\delta)\le0,
\qquad
\mathcal P_E(h-k_\delta)\ge0,
\qquad h-k_\delta>0
\quad(0<R<b).
\tag{13.12}
$$

Both barriers, after an outer cutoff, belong to the completed domain:
$k_\delta/h=R^\delta b_\delta$, whose transformed energy near zero is
$O(\int_0^bR^{2\delta-1}dR)<\infty$; the constant transformed part is
approximated by (12.13).

The weak comparison principle needed in this ball has a coercive form
proof. From (12.6)--(12.7), for $u$ in the completed domain supported in
$R<b$,

$$
\overline q_{\mathrm c}[u]-E\|u\|_2^2
\ge(1-Kb-K|E|b^2)\mathcal E_H[u/H].
\tag{13.13}
$$

Choose $b$ so the coefficient is positive. On the compact collar
$b/2\le R\le b$, positivity and smoothness of $f$ allow constants
$d,D>0$ with
$d(h+k_\delta)\le f\le D(h-k_\delta)$.
For the lower comparison test (13.12) and (13.6) with
$u=(d(h+k_\delta)-f)_+$, which vanishes on this collar. In the ground
transform the positive-part chain rule makes the resulting left side
exactly $\overline q_{\mathrm c}[u]-E\|u\|_2^2$, and it is nonpositive.
The right side of (13.13) forces $u=0$. The test is legitimate in the
completed local domain; logarithmic cutoffs (12.13) approximate at the
source, and positive-part approximation preserves nonnegativity. Hence
the punctured smooth subsolution inequalities extend to this test.
Applying the same reasoning to $(f-D(h-k_\delta))_+$ proves the upper
comparison. Since $k_\delta/h=O(R^\delta)$, these two comparisons give
(13.1).

A positive completed ground state consequently satisfies
$\int R^{-2}|f|^2d\mu=\infty$. Every member of $\mathcal F_A$ has that
integral finite by (4.2) and localization, so no such state belongs to
$\mathcal F_A$. The original punctured core is dense in the completed
form norm; normalization of its approximants shows that its normalized
infimum, that over $\mathcal F_A$, and the completed lowest energy are
all equal. If an original-domain minimizer existed, taking its absolute
value would give a nonnegative completed ground state in
$\mathcal F_A$, a contradiction. This proves nonattainment there and
attainment only in the completion. Norm equivalence at equality is
excluded because the free domain is complete whereas the original
critical form is not closed. $\square$

**Corollary 13.2 (local boundary, global data and the native dimensions).**
For the original both-wall model, the sharp semiboundedness boundary and
the failure of original-domain closedness and attainment at equality are
fixed by the source data in (10.6). Source position enters this boundary
only through $\rho(o)\det A(o)$; the anisotropy orientation and all
coefficient derivatives do not enter it. Two smooth models with identical
$r,\rho(o),\det A(o)$ have the same boundary even if their densities,
covariances, cylinder endpoints and full Green fields differ away from
the source. Their completed lowest energies are the variational minima
of their respective global forms (12.3); the equal-boundary assertion
does not identify those forms. Outside the both-wall row, every positive
coupling still
collapses as in the original volume's Theorem 3.1. Thus this classification
retains current-ray dimension three, direct rank two, growth $(2,3)$ and
homogeneous volume exponent four as distinct quantities, and makes no
physical Euclidean-dimension assertion.

**Proof.** The boundary and endpoint-domain conclusions are Theorem 13.1
and (10.6). The global Green correction enters $W$ in (12.2), and the
global kinetic form and killed boundary remain in $\mathcal E_H$; they
are not removed by fixing the leading singular coefficient. The local
comparison (11.3) puts all coefficient derivatives into lower-order errors,
while (10.2) puts the source anisotropy into an exact graded coordinate
change whose volume factor is $\det A(o)$. The constants in the remainder
and lower bound are fixed-model constants, with no assertion of uniformity
as the source approaches a height face or the coefficients vary. The original
single-wall and neither-wall collapse witnesses, with homogeneous volume
exponents seven and eleven, are unchanged and are reused from Theorem
7.1. The dimension and control statements follow from (2.1)--(2.2), with
no new control or phase operation. The repo-derived content is the exact
native unit-source/angular/full-Green correspondence and its critical
form-domain and minimum classification. The cited Hardy, heat, compactness
and KLMN inputs are attributed intermediate results; no exhaustive
literature or priority assertion is needed for these conclusions.
$\square$

## 追加锚（本行以下为增补区）

## 14. Spatial saturation of the original unit-source multiplier

**Definition 14.1 (the fixed spatial family).** Assume the both-wall row
of §1, with every preparation mean, grouped phase, guard, height face,
periodic coordinate, density, covariance, source and clock fixed as in
(1.1), (2.1) and (10.2). Write $\Gamma=\Gamma_{A,o}$,
$c_G=(2\pi m_0)^{-1}$, and set, for $\epsilon>0$,

$$
\begin{aligned}
\Gamma_\epsilon&=\min\{\Gamma,c_G\epsilon^{-2}\},
&\Gamma_\epsilon(o)&=c_G\epsilon^{-2},\\
q_\epsilon[f]&=T_A[f]-g_{\mathrm c}\int\Gamma_\epsilon|f|^2d\mu,
&D(q_\epsilon)&=\mathcal F_A,\\
D_\epsilon&=g_{\mathrm c}(\Gamma-\Gamma_\epsilon)\ge0,
&\mathcal C_\epsilon&=\{\Gamma>c_G\epsilon^{-2}\}.
\end{aligned}
\tag{14.1}
$$

The value at the measure-zero source fixes a representative. This is
bounded multiplication on the original free domain. Its operator is
$K_\epsilon=L_A-g_{\mathrm c}\Gamma_\epsilon$ on $D(L_A)$.
Let $K_*$ be the operator of the completed form (12.3), and let
$E_\epsilon=\inf\sigma(K_\epsilon)$ and $E_*=\inf\sigma(K_*)$.
Throughout §§14–19 every limit is $\epsilon\downarrow0$ for one fixed
smooth model. Constants need not be uniform over different models.

**Proposition 14.2 (the actual changed set and its anisotropic scale).**
For some fixed $C,b>0$ and all sufficiently small $\epsilon$,

$$
\{R<\epsilon(1-C\epsilon)\}
\subset\Psi(\mathcal C_\epsilon)
\subset\{R<\epsilon(1+C\epsilon)\}\Subset\{R<b\}.
\tag{14.2}
$$

The inclusions concern the entire changed set on the original cylinder.
Moreover, on each compact subset of the frozen chart,

$$
\epsilon^2\Gamma_\epsilon(\Psi^{-1}\delta_\epsilon q)
\longrightarrow c_G\min\{R(q)^{-2},1\}
\tag{14.3}
$$

uniformly, including $q=0$ with the capped value. In the original source
chart (2.3), the corresponding gauge is

$$
\left(
 |B(x,y)^{\mathsf T}|^4
 +16\det(B)^2(z-xy/2)^2
\right)^{1/4}.
\tag{14.4}
$$

Thus horizontal displacement has scale $\epsilon$ and the adapted central
displacement has scale $\epsilon^2$. In particular the central displacement
is not the uncorrected increment of the original $\beta$ phase.

Proof. The full Green field is bounded outside each source neighbourhood,
as used in (12.5). Thus its superlevel set in (14.1) is contained in the
injective source chart for small $\epsilon$. Equation (11.1), multiplied
by $c_G^{-1}R^2$, gives $\Gamma/(c_GR^{-2})=1+O(R)$.
Comparing this with $R^2/\epsilon^2$ proves (14.2); the same inequalities
for $R\ll\epsilon$ show that a whole source neighbourhood is capped.
On any annulus bounded away from zero, the error in the rescaled
uncapped field is $O(\epsilon/R)$. Taking the minimum is a Lipschitz
operation. On a fixed sufficiently small ball about zero both sides of
(14.3) are exactly $c_G$ for small $\epsilon$. These observations prove
uniform convergence on compact sets. Formula (14.4) is precisely (10.1),
without another coordinate or measure normalization. Since
$y=2(\alpha-\alpha_o)$ and $z=-r(\beta-\beta_o-c(k_o)y)$, it also gives
the stated native phase correspondence. $\square$

## 15. Selection of the completed operator and of its normalized ground state

**Theorem 15.1 (the realization selected by spatial saturation).** There
is a common $\beta>0$ such that

$$
\|(K_\epsilon+\beta)^{-1}-(K_*+\beta)^{-1}\|_{2\to2}
\longrightarrow0.
\tag{15.1}
$$

The lowest eigenvalues are simple, their normalized ground states can be
chosen strictly positive, and these choices are unique. Write them as
$f_\epsilon$ and $f_*$. Then

$$
\begin{aligned}
E_\epsilon&\downarrow E_*,& E_\epsilon&>E_*,\\
\|f_\epsilon-f_*\|_{L^2(\mu)}&\longrightarrow0,&
\overline q_{\mathrm c}[f_\epsilon-f_*]
 +\beta\|f_\epsilon-f_*\|_2^2&\longrightarrow0.
\end{aligned}
\tag{15.2}
$$

The associated rank-one orthogonal spectral projections converge in
operator norm. On every compact subset of $\Omega\setminus\{o\}$,
$f_\epsilon\to f_*$ with every ordinary smooth derivative, hence with
every horizontal derivative. Norm and source mass are retained in these
limits. The limiting form domain is exactly $H\mathcal W_H$ in (12.3).

Proof. Put $\mathcal Q=D(\overline q_{\mathrm c})$. Theorem 12.2 gives a
common lower bound $-B$ and a compact embedding $\mathcal Q\hookrightarrow
L^2(\mu)$. For $f\in\mathcal F_A$ the exact identity is

$$
q_\epsilon[f]=\overline q_{\mathrm c}[f]
 +\int D_\epsilon|f|^2d\mu.
\tag{15.3}
$$

The second term is finite by (13.2). Choose $\beta>B+1$.
If $f_n\rightharpoonup f$ in $L^2$ and $\epsilon_n\downarrow0$, a bounded
sequence of shifted $q_{\epsilon_n}$ values is bounded in the Hilbert
space $\mathcal Q$ with shifted norm. Weak lower semicontinuity there
proves

$$
\overline q_{\mathrm c}[f]+\beta\|f\|_2^2
\le\liminf_n\{q_{\epsilon_n}[f_n]+\beta\|f_n\|_2^2\}.
\tag{15.4}
$$

For the opposite approximation use the punctured core dense in
$\mathcal Q$. For each one of its elements $v$, the Green field is
bounded on its support, so $q_\epsilon[v]=\overline q_{\mathrm c}[v]$
for all sufficiently small $\epsilon$. A diagonal choice of core
approximations gives recovery for every $f\in\mathcal Q$.
Minimizing the strictly convex shifted resolvent functional with these
two inequalities proves strong resolvent convergence: each weak
accumulation point is the unique minimizer of the limiting functional,
and the quadratic identity at its minimum gives strong $L^2$
convergence. This is the usual variational proof of the monotone-form
convergence principle, with the actual closure and recovery core
identified here.

More is available because of compactness. For $\|x\|_2\le1$, the vectors
$(K_\epsilon+\beta)^{-1}x$ are uniformly bounded in $\mathcal Q$ by
(15.3) and their resolvent equation. Their union is therefore relatively
compact in $L^2$. To see that strong convergence upgrades to (15.1), take
unit vectors $x_n\rightharpoonup x$ and any $\epsilon_n\downarrow0$.
Every strong accumulation point $y$ of
$(K_{\epsilon_n}+\beta)^{-1}(x_n-x)$ satisfies

$$
\langle y,z\rangle
 =\lim_n\langle x_n-x,(K_{\epsilon_n}+\beta)^{-1}z\rangle=0
\quad(z\in L^2).
$$

It is zero. The limiting resolvent is compact as well, which proves
operator norm convergence by contradiction. The continuous spectral
calculus, or a contour separating its largest eigenvalue, then gives
convergence of the lowest spectral projection, once simplicity is checked.

Each finite-resolution form is a bounded attractive perturbation of the
free form. Its compactness is that of $\mathcal F_A$. The positive free
heat kernel and the bounded-potential product formula make its semigroup
positivity improving: for a nonzero nonnegative datum it dominates the
strictly positive free evolution. Its lowest eigenspace is therefore
simple, with a strictly positive normalized eigenfunction. These are
standard compact spectral and positivity arguments, applied on the actual
periodic cylinder, without an inner boundary. For the completed form,
Theorem 13.1 supplies a positive ground state. Its simplicity also follows
from the following exact ground transform, which will be needed below.
Define

$$
d\nu_*=f_*^2d\mu,\qquad
\mathscr A[u]=\int f_*^2\langle A Xu,Xu\rangle d\mu.
\tag{15.5}
$$

For a punctured-core $f$, integration against the equation for $f_*$ gives

$$
\overline q_{\mathrm c}[f]-E_*\|f\|_2^2
 =\mathscr A[f/f_*].
\tag{15.6}
$$

Taking the closure in the norm on either side extends (15.6) to all of
$\mathcal Q$. In this statement the domain on the right is the closure
of the quotients of punctured-core functions in
$\mathscr A+\|\cdot\|_{L^2(\nu_*)}^2$; it is not an imposed larger
weighted domain. Local testing away from $o$ identifies its derivatives
with the usual weak horizontal derivatives. A second ground state has
zero energy in (15.6). Its quotient has zero horizontal derivatives,
and the bracket-generating frame on the connected punctured cylinder
makes that quotient constant. This proves simplicity.

The positive normalization fixes the sign in projection convergence.
Min-max, (15.3), and the recovery core give $E_\epsilon\downarrow E_*$.
Moreover $E_*\le\overline q_{\mathrm c}[f_\epsilon]\le E_\epsilon$.
Together with $L^2$ convergence and weak compactness in $\mathcal Q$,
this gives convergence of the shifted Hilbert norms, hence strong
convergence in that space. Equality $E_\epsilon=E_*$ would force
$f_\epsilon=f_*$ in (15.6), contrary to
$f_*\notin\mathcal F_A$ in Theorem 13.1. This proves all assertions in
(15.2). The compactness proof in Theorem 12.2 gives uniformly vanishing
mass in shrinking source balls for these states; their limiting norm is
one, so no source or exterior mass is missing. Finally the capped
potential equals the smooth full potential on each fixed compact set
away from $o$ for all small $\epsilon$. Interior estimates for the fixed
smooth Hörmander operator, followed by iteration of the eigenvalue
equation, upgrade $L^2$ convergence there to smooth convergence. $\square$

## 16. The scalar trace of the globally normalized critical ground state

**Theorem 16.1 (positive source trace, including all angular directions).**
There are numbers $a_*>0$ and $\gamma\in(0,1)$, depending on the fixed
model and the normalized ground state, for which

$$
\frac{f_*(\Psi^{-1}q)}{h(q)}=a_*+O(R(q)^\gamma)
\quad(R\downarrow0).
\tag{16.1}
$$

The error is uniform over the whole gauge sphere, including the central
axis. On every fixed compact annulus, for each integer $j\ge0$,

$$
\left\|
 \frac{f_*(\Psi^{-1}\delta_s\,\cdot)}{h(\delta_s\,\cdot)}-a_*
\right\|_{C^j}\le C_j s^\gamma.
\tag{16.2}
$$

Here $C^j$ is taken in the smooth Cartesian coordinates of the annulus.
Thus $a_*$ is the scalar limit in the question, rather than just the two
comparison constants of (13.1).

Proof. Set $v=f_*/h$ on a source ball. By (13.1) it is bounded above
and below by positive constants. In the weighted local completion it
solves

$$
\mathscr B_h v=(E_*-W)v,\qquad
\mathscr B_h=-\frac1{mh^2}\operatorname{div}_H(mh^2C\nabla_H),
\qquad |(E_*-W)v|\le K/R.
\tag{16.3}
$$

The point has zero capacity for this weighted energy by (12.13).
The local Dirichlet problem on a sufficiently small source ball is
coercive by (12.7). These two facts allow weak testing through the point;
no point value or inner boundary data are prescribed.

Use the function $b_\delta=1+\delta^2w$ constructed in (13.7)–(13.10),
with one fixed sufficiently small $0<\delta<1$. That computation and
(11.3) imply, after reducing the ball,

$$
\mathscr B_h(R^\delta b_\delta)
 \le-\kappa R^{\delta-2},\qquad \kappa>0.
\tag{16.4}
$$

For $R<r$ the nonnegative function

$$
\psi_r=K_1r^{1-\delta}
 \{r^\delta\max_{\overline J}b_\delta-R^\delta b_\delta\}
\tag{16.5}
$$

has supremum at most $K_2r$, and, with $K_1$ fixed sufficiently large,
$\mathscr B_h\psi_r\ge K/R$. Indeed
$r^{1-\delta}R^{\delta-2}\ge R^{-1}$ for $R\le r$.
Let $z_r$ be the $\mathscr B_h$-harmonic replacement of $v$ in
$R<r$: $v-z_r$ is in the local zero-boundary weighted completion.
Existence follows by minimizing the weighted Dirichlet energy.
Testing the difference equation with its positive and negative parts
and using (16.5) gives

$$
\|v-z_r\|_{L^\infty(R<r)}\le K_2r.
\tag{16.6}
$$

All comparisons include the point by its zero capacity. For example
first use the logarithmic cutoffs (12.13) and then pass in the energy
norm. The barriers in (16.5) belong to that norm, so no source boundary
term survives.

The harmonic replacement has a scale-uniform oscillation contraction.
To verify this without asserting a Harnack theorem at the singular
point, rescale the connected annulus $r/4\le R\le r/2$ to a fixed
annulus. There $h^2$ is smooth and positive, the Hörmander frame is
fixed, and all coefficients and horizontal drifts of the rescaled
$\mathscr B_h$ are uniformly bounded with uniformly positive horizontal
covariance. The ordinary local Hörmander Harnack inequality, joined by a
finite chain of balls in a larger punctured annulus, has a constant $C$
independent of small $r$. Apply it to $z_r-m$ and $M-z_r$, where
$m=\inf_{R<r}z_r$ and $M=\sup_{R<r}z_r$. Write $d=M-m$.
Either the infimum of $z_r-m$ on this annulus is at least $d/(2C)$,
or its supremum is at most $d/2$. The weak maximum principle in the
inner ball, again using zero capacity at the point, consequently gives

$$
\operatorname{osc}_{R<r/4}z_r
 \le\vartheta\operatorname{osc}_{R<r}z_r,
\qquad \vartheta=1-(2C)^{-1}<1.
\tag{16.7}
$$

Combining (16.6)–(16.7) gives
$\operatorname{osc}_{R<r/4}v\le\vartheta
\operatorname{osc}_{R<r}v+K_3r$.
Iteration on $r,r/4,r/16,\ldots$ proves (16.1), with any suitably
smaller positive exponent than $-\log\vartheta/\log4$ and one.
The nested essential ranges shrink to one number. The positive bounds
from (13.1) make that number strictly positive. Smoothness off the source
makes the resulting estimate pointwise in every direction.

For the derivative assertion, the remainder (11.1) has the following
annular derivative consequence:

$$
\|s^2\Gamma(\Psi^{-1}\delta_s\,\cdot)-c_GR^{-2}\|_{C^j(K)}
 \le C_{K,j}s
\quad(K\Subset\mathbb R^3\setminus\{0\}).
\tag{16.8}
$$

Here is why no derivative of a bare pointwise estimate is being assumed.
The difference on the left is $O(s)$ in supremum norm by (11.1).
Its equation on a slightly larger annulus has a smooth right side
$O(s)$ in every fixed derivative, obtained by applying the rescaled
operator to $c_GR^{-2}$ and using (11.2)–(11.3). The rescaled smooth
coefficients converge in every derivative to the frozen ones.
Interior subelliptic estimates and Sobolev embedding, iterated on nested
annuli, therefore give (16.8). Apply the same interior estimates to
(16.3) after rescaling. Its right side is $O(s)$ in smooth annular
coefficients times $v$, and $v-a_*=O(s^\gamma)$ in supremum norm.
Iteration proves (16.2), reducing $\gamma$ if necessary. $\square$

## 17. Sharp energy transfer and the entire logarithmic transition

**Definition 17.1 (angular constants and the logarithmic mean).** Put

$$
M_\phi=\int_J\phi^2da,\qquad
C_\phi=\int_Jc\phi^2da,\qquad
k_\phi=\frac\pi2 C_\phi,\qquad
\mathsf K=a_*^2m_0k_\phi.
\tag{17.1}
$$

Fix $b>0$ sufficiently small for (16.1), set $L=\log(b/\epsilon)$,
and write

$$
u_\epsilon=f_\epsilon/f_*,\qquad
p_\epsilon(t)=\frac1{2\pi C_\phi}
 \int_J\int_0^{2\pi}c\phi^2u_\epsilon(R,a,\theta)\,d\theta da,
\quad R=e^t.
\tag{17.2}
$$

Here and below a quotient on the cylinder is pulled back by $\Psi^{-1}$
when it is evaluated at chart coordinates. The global measure $\nu_*$
in (15.5) has total mass one.

**Theorem 17.2 (the sharp gap and all-mode logarithmic profile).** For
every fixed model in Definition 14.1,

$$
L(E_\epsilon-E_*)\longrightarrow
\mathsf K=a_*^2\frac{\pi m_0}{2}C_\phi.
\tag{17.3}
$$

The mean has strong endpoint control:

$$
p_\epsilon(\log\epsilon+sL)\longrightarrow s
\quad\hbox{in }H^1(0,1).
\tag{17.4}
$$

For the full, unrestricted angular state,

$$
\frac{f_\epsilon(\Psi^{-1}(\epsilon e^{sL},a,\theta))}
 {h(\epsilon e^{sL},a,\theta)}
\longrightarrow a_*s
\quad\hbox{in }L^2((0,1)\times J\times\mathbb T,
                         \phi^2\,ds\,da\,d\theta).
\tag{17.5}
$$

For $0<\eta<1/2$, a fixed compact Cartesian annulus $K$, and each fixed
$j$, the convergence on intermediate scales also satisfies

$$
\sup_{\eta\le s\le1-\eta}
\left\|
 \frac{f_\epsilon(\Psi^{-1}\delta_{\epsilon e^{sL}}\,\cdot)}
 {h(\delta_{\epsilon e^{sL}}\,\cdot)}-a_*s
\right\|_{C^j(K)}\longrightarrow0.
\tag{17.6}
$$

These assertions include every angular mode, without imposing symmetry
on the actual coefficients or ground states.

Proof. Write $d_\epsilon=E_\epsilon-E_*$ and use the exact transform
(15.6). The normalized eigenstate obeys

$$
\mathscr A[u_\epsilon]
 +\int D_\epsilon u_\epsilon^2d\nu_*=d_\epsilon,
\qquad \|u_\epsilon\|_{L^2(\nu_*)}=1,
\qquad u_\epsilon\to1\text{ in }L^2(\nu_*).
\tag{17.7}
$$

Locally away from the source the last convergence is smooth. From
(10.2), (16.1) and (16.2), the local density and matrix of $\mathscr A$
are

$$
f_*^2mC=a_*^2m_0h^2\{I+O(R^\gamma)\}.
\tag{17.8}
$$

The exponent may be decreased to be below one. This is a matrix estimate,
so it controls arbitrary angular derivatives and cross terms.

Here are the two elementary angular facts used in the proof. For a real
chart function $u$, let $p$ be its mean (17.2) and $w=u-p(\log R)$.
Formula (12.8) gives the exact orthogonal decomposition on any logarithmic
interval $I_t$:

$$
\mathcal E_0[u;I_t]
 =k_\phi\int_{I_t}|p'(t)|^2dt+\mathcal E_0[w;I_t].
\tag{17.9}
$$

Indeed $\int c\phi^2w=0$ on each slice, and the integral of the
$\theta$ derivative in the cross term is zero. No estimate discards a
mode. There is also a constant independent of $t$ such that

$$
\int_t^{t+1}\int_{J\times\mathbb T}\phi^2|w|^2
 \le C\mathcal E_0[w;(t-1,t+2)].
\tag{17.10}
$$

To justify (17.10), dilate to the fixed compact annulus
$1\le R\le e$ inside $e^{-1}<R<e^2$. Cover it by a finite connected
chain of horizontal metric balls compactly contained in the larger
annulus. The usual local horizontal Poincaré inequality on those balls,
and comparison of their smooth positive weights with $h^2$, bound the
squared norm on the middle annulus modulo a constant by the energy on
the larger annulus. The zero $c\phi^2$ mean on every slice removes that
constant: integrate that mean over the middle annulus and apply
Cauchy–Schwarz to $w$ minus the constant. On this fixed annulus the
polar integral in (17.10) is comparable with the Cartesian volume
integral. Dilation gives the same constant at every $t$. This argument
covers the central axis in ordinary Cartesian balls; it uses neither
a boundary condition at $a=\pm\pi/2$ nor a zeroth-mode restriction.
The local Poincaré inequality here is the standard smooth Hörmander
one; the source singularity is outside every ball where it is applied.

For an upper bound choose a trial quotient which is zero for $R\le2\epsilon$,
is $\log(R/(2\epsilon))/\log(b/(2\epsilon))$ between $2\epsilon$ and $b$,
and equals one outside $R<b$. Its product with $f_*$ belongs to
$\mathcal F_A$, by localization of (12.3), and its deficit term vanishes
by (14.2). Corners may be approximated in the free norm. For a radial
quotient the exact frozen energy is $k_\phi\int|u_t|^2dt$.
In (17.8), the integral of the error along this interval is bounded by
$C\int_0^bR^\gamma dR/R<\infty$. Its actual energy is consequently
$\mathsf K/L+O(L^{-2})$. Its squared norm is $1+O(L^{-1})$, because

$$
\int_{R<b}\log(b/R)\,d\nu_*<\infty,
\qquad \nu_*(R<2\epsilon)=O(\epsilon^2).
$$

The ground transform and normalization give

$$
0<d_\epsilon\le\mathsf K/L+O(L^{-2}).
\tag{17.11}
$$

For the converse bound note first that, on $R<\epsilon/2$,
$D_\epsilon\ge c_1R^{-2}$ for all small $\epsilon$, by (11.1).
Equations (17.7)–(17.8) therefore imply

$$
\int_{\log(\epsilon/4)}^{\log(\epsilon/2)}
 \int\phi^2u_\epsilon^2\le C d_\epsilon,
\qquad
\int_{\log(\epsilon/4)}^{\log\epsilon}
 |p_\epsilon'|^2\le C d_\epsilon.
\tag{17.12}
$$

Cauchy–Schwarz, first for the mean and then along this interval, gives
$|p_\epsilon(\log\epsilon)|\le C\sqrt{d_\epsilon}=o(1)$.
For every fixed small $d>0$,
$p_\epsilon(\log d)\to1$ by Theorem 15.1. If
$\eta_d\downarrow0$ bounds the relative matrix error in (17.8) on
$R<d$, then (17.7), (17.9), and the one-dimensional Cauchy–Schwarz
inequality give

$$
d_\epsilon\ge a_*^2m_0(1-\eta_d)k_\phi
 \frac{(p_\epsilon(\log d)-p_\epsilon(\log\epsilon))^2}
 {\log(d/\epsilon)}.
\tag{17.13}
$$

Let $\epsilon\downarrow0$, then $d\downarrow0$. Together with (17.11)
this proves (17.3). The trial function alone was only its upper half;
(17.12)–(17.13) supply the lower half for the actual eigenstates.

The same inequalities imply saturation and localization of their energy.
For every fixed source radius $d$, the $\mathscr A$ energy outside that
ball is $o(L^{-1})$. Indeed apply (17.13) at any smaller fixed radius
$d'<d$; its liminf consumes at least
$(1-\eta_{d'})\mathsf K$ of the total rescaled energy, and then let
$d'\downarrow0$. The identical argument gives

$$
L\mathscr A[u_\epsilon;R<\epsilon]\to0,
\qquad
L\int D_\epsilon u_\epsilon^2d\nu_*\to0.
\tag{17.14}
$$

To compare the remaining annular energy with its frozen value, split
(17.8) at $R=d$. On the inner part its error is at most $\eta_d$ times
the energy; on the outer part the energy is $o(L^{-1})$. Thus

$$
L\mathcal E_0[u_\epsilon;
                 \log\epsilon<t<\log b]\longrightarrow k_\phi.
\tag{17.15}
$$

Set $P_\epsilon(s)=p_\epsilon(\log\epsilon+sL)$. Its endpoint values
tend to zero and one by (17.12) and smooth convergence at $R=b$.
Equations (17.9) and (17.15) give
$\limsup\int_0^1|P_\epsilon'|^2\le1$. The endpoint difference tends to
one, so the reverse bound and equality case of Cauchy–Schwarz imply
$P_\epsilon'\to1$ in $L^2$ and $P_\epsilon\to s$ in $H^1$.
This proves (17.4).

Sum (17.10) over the interval from $\log\epsilon$ to $\log b$.
Only boundedly overlapping enlarged intervals occur. On the slightly
larger chart interval the energy is $O(L^{-1})$, by (17.7)–(17.8), and
(17.9) bounds the energy of $w$ by that of $u$. Consequently

$$
\frac1L\int_{\log\epsilon}^{\log b}
 \int\phi^2|u_\epsilon-p_\epsilon|^2
 =O(L^{-2}).
\tag{17.16}
$$

Together with (17.4) this proves full-angular $L^2$ convergence of the
quotient $u_\epsilon$ to $s$. Multiplication by
$f_*/h=a_*+O(R^\gamma)$ proves (17.5): the error tends to zero at every
$s<1$, is uniformly bounded, and $P_\epsilon$ is uniformly bounded by
its $H^1$ norm. The nonconstant remainder is controlled by (17.16).
Thus the integration includes both ends of the growing annulus.

For (17.6), any unit-sized logarithmic annulus about
$R=\epsilon e^{sL}$, $\eta\le s\le1-\eta$, stays away from the changed
set and shrinks to the source. Its quotient solves
$\mathscr B_*u_\epsilon=d_\epsilon u_\epsilon$, with
$\mathscr B_*=-(mf_*^2)^{-1}\operatorname{div}_H(mf_*^2C\nabla_H)$.
After dilation its smooth coefficients are uniformly controlled by
(16.2), and the right side has the extra factor $R^2$.
The local version of (17.10), (17.16), and the uniform convergence of
$P_\epsilon$ show $L^2$ convergence to the constant $s$ on every such
rescaled annulus. Interior subelliptic estimates upgrade it to each
$C^j$ norm on a smaller annulus. If uniformity in $s$ failed, the same
argument along a failing sequence of scales would give a contradiction.
This proves (17.6). $\square$

**Theorem 17.3 (separate resources of the actual finite-resolution states).**
With

$$
V_{\rm raw}[f]=\int\Gamma|f|^2d\mu,\qquad
V_{\rm cap}[f]=\int\Gamma_\epsilon|f|^2d\mu,
\tag{17.17}
$$

where the second notation is evaluated at its indicated resolution,
all three finite-resolution resources satisfy

$$
\begin{aligned}
\frac{V_{\rm raw}[f_\epsilon]}L&\longrightarrow
                    \frac{a_*^2M_\phi}{12},\\
\frac{V_{\rm cap}[f_\epsilon]}L&\longrightarrow
                    \frac{a_*^2M_\phi}{12},\\
\frac{T_A[f_\epsilon]}L&\longrightarrow
                    \frac{g_{\mathrm c}a_*^2M_\phi}{12}.
\end{aligned}
\tag{17.18}
$$

In particular the selected completed state is approached with divergent
separate kinetic and attraction costs, although its energy is finite.

Proof. On $R<\epsilon/2$ the deficit is at least a fixed positive
multiple of $\Gamma$, so (17.7) bounds the raw attraction there by
$C d_\epsilon$. On $\epsilon/2<R<\epsilon$, the mean is
$O(\sqrt{d_\epsilon})$ by (17.12) and the derivative bound. Applying
(17.10) on this fixed-width logarithmic collar bounds the angular
remainder in squared norm by $C d_\epsilon$. Hence

$$
V_{\rm raw}[f_\epsilon;R<\epsilon]=O(L^{-1}).
\tag{17.19}
$$

Outside $R<b$ the full Green multiplier is bounded, so its contribution
is $O(1)$. On the middle annulus use its exact raw volume and density:
if $v_\epsilon=f_\epsilon/h$, then

$$
\Gamma f_\epsilon^2d\mu
 =\left\{\frac1{8\pi}+O(R)\right\}
       \phi^2v_\epsilon^2\,dt\,da\,d\theta.
\tag{17.20}
$$

The coefficient $1/(8\pi)$ is $m_0c_G/4$; it retains both the raw
Jacobian $1/4$ and the full $2\pi$ angular period. Divide the annular
integral by $L$ and use (17.5). The error in (17.20) vanishes: below a
fixed $d$ it is bounded by $Cd$ times a uniformly bounded rescaled
squared norm; above $d$ the interval has fixed logarithmic length and
the eigenfunctions converge smoothly. The main term is

$$
\frac1{8\pi}\,a_*^2
 \int_0^1s^2ds\int_J\int_0^{2\pi}\phi^2d\theta da
 =\frac{a_*^2M_\phi}{12}.
\tag{17.21}
$$

This proves the raw law. The nonnegative difference of raw and capped
attraction is bounded by $d_\epsilon/g_{\mathrm c}$ in (17.7), so the
capped law has the same leading coefficient. Finally the exact
finite-domain identity
$T_A[f_\epsilon]=E_\epsilon+g_{\mathrm c}V_{\rm cap}[f_\epsilon]$
and boundedness of $E_\epsilon$ prove the kinetic law. No subtraction of
infinities is used for any finite $\epsilon$. $\square$

## 18. The source-regular capped core and its matched normalization

**Theorem 18.1 (unique inner profile and the actual source amplitude).**
There is exactly one positive real function $Z$ on the frozen group which
is a weak solution of

$$
(-\Delta_H-\lambda_0\min\{R^{-2},1\})Z=0
\quad\hbox{on }\mathbb R^3,
\tag{18.1}
$$

is smooth at the source, and has logarithmic coefficient one at infinity.
More precisely, it is smooth on $R<1$ and on $R>1$, belongs to
$W^{1,2}_{H,\mathrm{loc}}(\mathbb R^3)$, is continuous and positive
everywhere, and for one real $\kappa_{\rm cap}$ satisfies

$$
\frac{Z(q)}{h(q)}=\log R(q)+\kappa_{\rm cap}+o(1)
\quad(R\to\infty).
\tag{18.2}
$$

The error is uniform over all angular directions. On compact rescaled
annuli it tends to zero with every smooth derivative after subtracting
$\log R+\kappa_{\rm cap}$. The function $Z$ is invariant under rotations
of $(\xi,\eta)$; this invariance is a conclusion about the frozen core,
not a restriction on the original model.

For the actual normalized eigenstates,

$$
F_\epsilon(q):=\epsilon L
 f_\epsilon(\Psi^{-1}\delta_\epsilon q)
 \longrightarrow a_*Z(q).
\tag{18.3}
$$

Convergence holds locally uniformly and strongly in
$W^{1,2}_{H,\mathrm{loc}}$, and in every $C^j$ norm on compact subsets
of $R<1$ or $R>1$. In particular it includes the source:

$$
\epsilon L f_\epsilon(o)\longrightarrow a_*Z(0)>0.
\tag{18.4}
$$

The normalization of $Z$ is equivalently the exact flux condition

$$
\lambda_0\int_{R<1}(R^{-2}-1)hZ\,dq=k_\phi.
\tag{18.5}
$$

Proof. A linear charge identity fixes the inner amplitude more strongly
than the quadratic energy estimate (17.7). The finite-resolution
quotient satisfies, weakly on its actual transformed domain,

$$
\mathscr B_*u_\epsilon+D_\epsilon u_\epsilon
 =d_\epsilon u_\epsilon.
$$

Test it with the logarithmic source cutoffs approaching the constant one.
Their products with $f_*$ belong to $\mathcal F_A$; outside the source
chart this follows directly from (12.3). The $\mathscr A$ energy of
these cutoffs tends to zero by (13.1) and (12.13). The kinetic pairing
therefore vanishes in the limit. The potential pairing is absolutely
integrable: near zero $f_\epsilon$ is smooth, because its potential is
constant on an entire source neighbourhood, whereas $f_*=O(R^{-1})$;
thus $D_\epsilon f_\epsilon f_*d\mu=O(R^{-3})dq$ for each fixed
$\epsilon$. Dominated convergence gives the exact identity

$$
Q_\epsilon:=\int D_\epsilon u_\epsilon d\nu_*
 =d_\epsilon\int u_\epsilon d\nu_*.
\tag{18.6}
$$

Since $\nu_*$ is a probability measure and $u_\epsilon\to1$ in its
$L^2$ norm, (17.3) implies

$$
LQ_\epsilon\longrightarrow a_*^2m_0k_\phi.
\tag{18.7}
$$

This identity tests the original eigenproblem; it adds no counterterm or
source condition to the approximating operators.

Rescale (18.6) in the source chart, using (14.2), (16.1), and
$g_{\mathrm c}c_G=\lambda_0$. On $R<2$ its expression is

$$
LQ_\epsilon
 =a_*m_0\lambda_0\int
 \big(R^{-2}-1+e_\epsilon(q)\big)_+
 h(q)F_\epsilon(q)\{1+O(\epsilon^\gamma R^\gamma)+O(\epsilon R)\}\,dq,
\quad |e_\epsilon(q)|\le C\epsilon/R.
\tag{18.8}
$$

The integral vanishes outside $R<1+C\epsilon$. On the fixed annulus
$1/4<R<1/2$ its kernel has a uniform strictly positive lower bound.
The rescaled equation for $F_\epsilon$ has smooth uniformly converging
horizontal coefficients and bounded potential, converging locally
uniformly to that in (18.1). This includes zero by (14.3). Uniform local
Hörmander Harnack inequalities connect that annulus to every fixed
compact set. Hence the bounded charge (18.7) bounds $F_\epsilon$ on
every such set. Local Hölder and energy estimates give compactness
locally uniformly and weakly in $W_H^{1,2}$. On $R<1$ and $R>1$,
(16.8) and the rescaled equation give smooth compactness. Differences
of the weak equations, tested with a compactly supported cutoff times
the difference of the functions, upgrade local horizontal energy
convergence to strong convergence: the coefficients converge smoothly,
the potentials converge uniformly, and the functions converge uniformly.
This last argument works across $R=1$ as well and asserts only the
stated weak and first-derivative regularity there.

Let $F$ be any subsequential limit. It is smooth at zero, solves (18.1),
and is nonnegative. The kernel in (18.8) is bounded by a constant times
$(R^{-2}+1)h=O(R^{-3}+R^{-1})$, integrable on $R<2$. Compact uniform
bounds thus allow passage to the limit, including zero and the moving
cap boundary. Equations (18.7)–(18.8) give

$$
\lambda_0\int_{R<1}(R^{-2}-1)hF\,dq=a_*k_\phi.
\tag{18.9}
$$

It is positive. The strong maximum principle makes $F$ positive
everywhere. It remains to prove that this charge selects a unique
positive entire profile, and that its coefficient at infinity is the
one claimed. This is an all-angular assertion.

For any positive entire source-regular solution $F$ of (18.1), set
$v=F/h$ and $P_0=\lambda_0(R^{-2}-1)_+$. The frozen ground transform
says

$$
\mathscr B_0v+P_0v=0,\qquad
\mathscr B_0=-h^{-2}\operatorname{div}_H(h^2\nabla_H).
\tag{18.10}
$$

Near zero $v=O(R)$ and its transformed energy is finite. Integrating
(18.10) over a ball, or first testing with radial cutoffs, gives for
$R>1$ the constant outward flux

$$
k_\phi p'(\log R)
 =\int_{R<1}P_0hF\,dq,
\qquad
p(t)=\frac1{2\pi C_\phi}\int c\phi^2v(t,a,\theta)\,da d\theta.
\tag{18.11}
$$

There is no inner flux: source regularity makes it tend to zero like
$O(R)$ as the inner radius tends to zero. Consequently
$p(t)=\beta t+\alpha$ for $t>0$, with
$\beta=k_\phi^{-1}\int P_0hF>0$. Uniform Harnack on a fixed rescaled
annulus gives $\sup_{R=e^t}v\le C p(t)$ for $t\ge1$, so $v=O(1+t)$.

The angular decay needed here has a direct energy proof. Put
$w=v-(\beta t+\alpha)$; it has zero $c\phi^2$ mean on every slice
and solves $\mathscr B_0w=0$ for $t>0$. Define

$$
\begin{aligned}
H_w(t)&=\int c\phi^2w^2\,da d\theta,\\
e_w(t)&=\frac14\int\phi^2
 \{c|w_t+\tan a\,w_\theta|^2
          +4c|w_a+\tfrac12w_\theta|^2\}\,da d\theta.
\end{aligned}
\tag{18.12}
$$

Differentiating twice and using the divergence equation gives

$$
H_w''(t)=8e_w(t)\ge0,
\qquad
\int_t^{t+1}H_w\le C\int_{t-1}^{t+2}e_w.
\tag{18.13}
$$

The second inequality follows from (17.10). In the first calculation,
solving the divergence equation for $cw_{tt}$ and integrating its
$w_{t\theta}$ term by parts gives the cross term
$4\int c\phi^2\tan a\,w_\theta w_t$ in $H_w''$.
The remaining terms are
$2\int c\phi^2(w_t^2+\tan^2a\,w_\theta^2)
 +8\int c\phi^2(w_a+w_\theta/2)^2$, which give exactly $8e_w$.
One may perform the integrations on Cartesian annuli and then use
(10.9); the collapsed angular coordinates create no axis boundary terms.

Here $H_w(t)=O((1+t)^2)$. A convex nonnegative function with this growth
and (18.13) must decrease to zero. Indeed, if its derivative is ever
positive, it stays positive. For all later $t$, (18.13) and convexity
then give

$$
H_w(t)\le C_1\{H_w'(t+2)-H_w'(t-1)\}
 \le C_1\{H_w(t+3)-H_w(t)\}.
$$

Iteration forces exponential growth, a contradiction. Thus its
derivative is nonpositive and tends to zero. Integrating (18.13) to
infinity now gives $\int_T^\infty H_w<\infty$; its decreasing limit is
zero. Also $\int_{t-1}^{t+2}e_w\to0$. The full weighted squared norm
of $w$ on each middle annulus tends to zero by (17.10), and interior
estimates for $\mathscr B_0$ turn this into smooth convergence on
rescaled compact annuli. It follows that

$$
F/h=\beta\log R+\alpha+o(1)
\tag{18.14}
$$

in the asserted all-angular sense.

Two positive source-regular solutions with the same $\beta$ have a
difference whose quotient by $h$ is bounded at infinity by (18.14) and
is $O(R)$ at zero. Test its equation (18.10) with its quotient times
the square of a cutoff equal to one on $R<e^T$, zero on $R>e^{2T}$,
and affine in $\log R$ between. Cauchy–Schwarz bounds the cutoff error
by $C/T$, since the quotient is bounded and the frozen energy of that
cutoff is $k_\phi/T$. Inner cutoffs have vanishing error by the $O(R)$
source behavior. Let $T\to\infty$. The nonnegative transformed energy
and $\int P_0h^2v^2$ both vanish. The quotient is constant, and the
latter integral forces that constant to be zero. This proves uniqueness
for each positive logarithmic coefficient.

Applied to (18.9), this proves $F=a_*Z$, with (18.2) and (18.5).
It also proves existence of $Z$ without assuming an exterior scattering
theorem. Every subsequence has that same limit, so (18.3) holds for the
whole family. Rotating $Z$ in the horizontal plane preserves (18.1),
source regularity, positivity, and coefficient one. Uniqueness proves
its rotational invariance. The common logarithmic coefficient in
(17.5) and (18.2) is fixed by the exact charge (18.6). This completes
the matching and proves (18.4). $\square$

**Theorem 18.2 (the actual cap deficit and the two core attractions).**
Define the finite strictly positive constant

$$
I_{\rm cap}=\int_{R<1}(R^{-2}-1)Z^2dq.
\tag{18.15}
$$

For the changed set $\mathcal C_\epsilon$ of (14.1),

$$
\begin{aligned}
L^2\{V_{\rm raw}[f_\epsilon]-V_{\rm cap}[f_\epsilon]\}
 &\longrightarrow\frac{a_*^2}{2\pi}I_{\rm cap},\\
L^2\int_{\mathcal C_\epsilon}\Gamma f_\epsilon^2d\mu
 &\longrightarrow\frac{a_*^2}{2\pi}\int_{R<1}R^{-2}Z^2dq,\\
L^2\int_{\mathcal C_\epsilon}\Gamma_\epsilon f_\epsilon^2d\mu
 &\longrightarrow\frac{a_*^2}{2\pi}\int_{R<1}Z^2dq.
\end{aligned}
\tag{18.16}
$$

Thus the deficit is of order $L^{-2}$, while both total attractions in
(17.18) are of order $L$.

Proof. Substitute $F_\epsilon$ from (18.3) and
$d\mu(\delta_\epsilon q)=\epsilon^4m(\delta_\epsilon q)dq$ in the
three actual integrals. The factors from the multiplier and squared
state are respectively $\epsilon^{-2}$ and
$\epsilon^{-2}L^{-2}$, so all powers of $\epsilon$ cancel.
The coefficient is $m_0c_G=1/(2\pi)$. The domains in the last two
integrals lie between $R<1-C\epsilon$ and $R<1+C\epsilon$ by (14.2).
The rescaled uncapped multiplier is $c_G(R^{-2}+O(\epsilon/R))$;
the capped multiplier on that set is exactly $c_G$.
The rescaled eigenfunctions are uniformly bounded on $R<2$ and converge
uniformly, including zero, by Theorem 18.1. The dominating function
$C(R^{-2}+1)$ is integrable there, with the raw four-dimensional
homogeneous volume $R^3dR\,da\,d\theta/4$. Dominated convergence and
the vanishing shell at $R=1$ prove (18.16). Positivity and finiteness of
(18.15) follow from source regularity and $Z>0$. $\square$

## 19. Density covariance, source correspondence and the scope of the limit

**Corollary 19.1 (raw-density covariance and the fixed native carrier).**
Under the constant change $\rho\mapsto c\rho$, $c>0$, with every other
original datum fixed, the differential operator $L_A$, the products
$g_{\mathrm c}\Gamma$ and $g_{\mathrm c}\Gamma_\epsilon$, and all the
energies $E_*,E_\epsilon$ are unchanged. The normalized states and trace
transform as

$$
f_*\mapsto c^{-1/2}f_*,\qquad
f_\epsilon\mapsto c^{-1/2}f_\epsilon,\qquad
a_*\mapsto c^{-1/2}a_*.
\tag{19.1}
$$

Consequently the energy and kinetic coefficients in (17.3) and (17.18)
are invariant, while each raw or capped attraction coefficient in
(17.18) and (18.16) is multiplied by $c^{-1}$. The frozen profile $Z$
and $\kappa_{\rm cap},I_{\rm cap}$ do not change.

All the conclusions in §§14–18 retain the same both-wall periodic
cylinder, original free domains at finite resolution, unit-source full
Green field, and covariance $2A\,dt$. The scalar $a_*$ and energy $E_*$
are those of the globally normalized completed eigenproblem. The common
frozen problem (18.1), with its proved uniqueness and normalization,
is the precise local profile shared by these fixed models after the
source-coordinate and density correspondences have been made.
The dimension statements remain current-ray dimension three, direct
rank two, growth $(2,3)$ and homogeneous volume exponent four. They
supply no additional assertion about a physical Euclidean dimension or
an acquisition map.

Proof. Multiplication of the density by $c$ cancels in the divergence
expression (11.2). The inverse kernel for a unit source relative to the
new measure is $\Gamma/c$. Equations (10.2), (10.6) give
$m_0\mapsto cm_0$, $c_G\mapsto c_G/c$, and
$g_{\mathrm c}\mapsto cg_{\mathrm c}$. Therefore the minimum defining
$\Gamma_\epsilon$ also divides by $c$, and both operator potentials
are unchanged. The unitary identification of the two Hilbert spaces
is multiplication by $c^{-1/2}$. It preserves kinetic and completed
form values, their domains under that identification, and all normalized
eigenvalues. Equations (16.1) and (18.3) give (19.1).
In the energy coefficient $a_*^2m_0k_\phi$ the two factors cancel;
in the kinetic coefficient $g_{\mathrm c}a_*^2M_\phi/12$ they also
cancel. Each attraction coefficient contains $a_*^2$ with no remaining
$m_0$, as follows from the raw source factor $m_0c_G=1/(2\pi)$.
This verifies the resource covariance separately from operator covariance.
The chart and (18.1) are unchanged, so uniqueness in Theorem 18.1 fixes
$Z$ and the other inner constants.

The carrier and clock assertions follow from (1.1), Definition 14.1 and
(2.1), (10.2). In particular (14.2) describes a multiplier's changed set;
it is not a Dirichlet hole. Equation (18.1) is a limit equation for
eigenstates, not the equation of a replacement Green source.
The globally normalized problem is retained throughout (15.5)–(18.8),
so the proof neither fixes $a_*$ by a local normalization nor identifies
the energies of different global models.

The full-Green normalization, unweighted angular Hardy constant,
critical completion and comparability used here are precisely
Theorems 10.2, 11.1, 12.2 and 13.1 of this volume. The local heat,
Hörmander regularity, Harnack and horizontal Poincaré tools are used on
smooth punctured annuli or for bounded potentials; the zero-capacity
extension through the source is proved with (12.13).
The compact form representation, bounded-potential product formula and
min-max tools have the same classical scopes as the Teschl inputs cited
in §§12–13.

The native temporal family in
[Critical cutoff spectral limits, Definition 31.1 and Theorems 32.2,
33.1](FIB_NATIVE_CRITICAL_CUTOFF_SPECTRAL_LIMITS.md) changes moving-time
multipliers and parameters. The positive-time threshold field on the
real cover in
[Long-time phase weak binding, Definition 70.1 and Proposition
70.2](FIB_NATIVE_LONG_TIME_PHASE_WEAK_BINDING.md) has the changed source
$SW_\tau=F(\tau;\cdot)$ and a different domain at infinity. Neither is
used to replace (14.1). The elementary bounded-cap lower bound is already
in [Continuation III, Specification
82.7](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md).
The added kinetic-law endpoint in its Theorem 87.4 and the planar window
bound in [Continuation II, Proposition
72.12](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_II.md)
have their stated different operators and boundaries. Their cap,
completion and logarithmic-capacity ideas are not new supplies of a
native spatial eigenstate asymptotic.

For comparison with primary literature, Abatangelo–Felli–Hillairet–Léna,
[Theorems 1.4, 1.7 and Appendix A](https://arxiv.org/html/1611.06750v1),
[DOI 10.4171/jst/251](https://doi.org/10.4171/jst/251), give the
simple-eigenvalue variation by eigenfunction capacity and its planar
logarithmic specialization for Euclidean Dirichlet holes. Vázquez–
Zographopoulos, [§§2.1, 2.3–2.4 and
4.2](https://arxiv.org/html/1102.5661), supply the Euclidean critical
weighted completion, logarithmic approximation and hidden-energy
context. Felli–Ferrero, [Theorem 2.1 and Corollaries
2.2–2.3](https://arxiv.org/html/1209.4852v1), prove critical-Hardy
cylindrical asymptotics for their Euclidean equation. Abatangelo–
Bonnaillie-Noël–Léna–Musolino, [Theorems 1.1 and
6.2](https://arxiv.org/html/1911.06686), exhibit the dependence of
small-hole eigenvalue changes on the normalized eigenfunction and hole
profile; their Theorem 6.2 concerns a positive vanishing order.
Pinchover–Tintarev, [Theorem
1.4](https://arxiv.org/html/math/0411658v1), is the elliptic
spectral-gap/null-state alternative. None of these statements directly
identifies the horizontal soft cap, its raw source density, angular
flux, or original-domain eigenstates here. The transfer in §§16–18 is
proved through those exact native objects, including the lower energy
bound, endpoint angular control and the linear charge (18.6).
These are source-specific ordinary mathematical deductions; the
attribution makes no exhaustive literature or priority assertion.
$\square$

## 追加锚（本行以下为增补区）

## 20. The fixed near-critical spatial family and its angular pencil

**Definition 20.1 (shared native data and parameters).** Retain the entire
both-wall model of §§1–2 and Definition 14.1. All preparations, means,
controls, guards, grouping, periodic phases, height killing, the original
interior unit source, smooth positive raw density and smooth SPD matrix
are fixed. The operator and clock are still those of (1.1), with control
covariance $2A\,dt$. Fix one $b>0$ in the injective chart allowed in §16.
Only the following multiplier and coupling vary:

$$
\begin{aligned}
L&=\log(b/\epsilon),&
g_{\epsilon,\lambda}&=g_{\mathrm c}(1+\lambda/L^2),\\
\Gamma_\epsilon&=\min(\Gamma,c_G\epsilon^{-2}),&
K_{\epsilon,\lambda}&=L_A-g_{\epsilon,\lambda}\Gamma_\epsilon,\\
D(q_{\epsilon,\lambda})&=\mathcal F_A,&
D(K_{\epsilon,\lambda})&=D(L_A).
\end{aligned}
\tag{20.1}
$$

For every fixed real $\lambda$, the coupling is positive for all
sufficiently small $\epsilon$. Let $E_{\epsilon,\lambda}$ and
$f_{\epsilon,\lambda}>0$ be the actual lowest energy and its positive
$L^2(\mu)$-normalized state. Bounded multiplication, compactness and the
positivity argument of §15 supply this simple eigenpair at each such
resolution. In formulas confined to one $\lambda$ suppress that index.
Write $F=K_*$, $\mathcal Q=H\mathcal W_H$, and
$\mathcal T=L_A-g_{\mathrm c}\Gamma$ for the uncapped critical expression.

The exact chart (10.1) has $d\mu=m(q)dq$, $C(0)=I_2$ and
$m_0=\rho(o)\det A(o)/(2r)$. Its frozen fields are
$U=\partial_\xi-\eta\partial_\tau/2$ and
$V=\partial_\eta+\xi\partial_\tau/2$. Throughout the append put

$$
\begin{gathered}
M=\int_J\phi^2da,\quad C=\int_Jc\phi^2da,\quad
k=\frac\pi2 C,\quad N=\frac k2,\quad K=m_0k,\\
\alpha=\frac{\lambda_0M}{C},\qquad
\lambda_D=\frac{\pi^2}{\alpha},\qquad
\nu=\frac\pi2,\qquad \lambda_Z=\frac{\nu^2}{\alpha},\\
\mathsf K=a_*^2K,\qquad
\mathsf D=\mathsf K\alpha=\frac{g_{\mathrm c}a_*^2M}{4}.
\end{gathered}
\tag{20.2}
$$

Here $c=\cos a$, $h=R^{-1}\phi(a)$, $c_G=(2\pi m_0)^{-1}$ and
$g_{\mathrm c}=2\pi m_0\lambda_0$ are exactly those of §§10–18.
The measure is $dq=R^3dR\,da\,d\theta/4$, with the full $2\pi$ angle.
The scalar product is linear in its first variable. The notation $K$
for the source Green pairing is distinct from the operator $K_*$ and
from the accepted energy coefficient $\mathsf K=a_*^2K$.

**Lemma 20.2 (the full angular pencil and the relevant detuning).** Put
$t=\log R$. In the frozen inverse-square region the expression on
$R^{-1}e^{in\theta-ina/2}w(t,a)$ is described by

$$
\begin{aligned}
P_{\gamma,n}(s)b
 &=-4(cb')'+\left(c+\frac{n^2\sin^2a}{c}
       -\gamma-cs^2-2ins\sin a\right)b,\\
P_{\gamma,n}(\partial_t)w&=E e^{2t}w,
\qquad \gamma=\frac{g}{2\pi m_0}.
\end{aligned}
\tag{20.3}
$$

At $\gamma=\lambda_0$ the only indicial root in the closed strip
$|\operatorname{Re}s|\le1$ is the double root $s=0$ in the $n=0$
sector; its solutions are $\phi$ and $t\phi$. Every other admissible
$L^2$ branch at the puncture has $\operatorname{Re}s>1$.
This separation persists near $\lambda_0$, except for the moving pair

$$
s_0(\gamma)^2=(\lambda_0-\gamma)M/C
                 +O((\gamma-\lambda_0)^2).
\tag{20.4}
$$

Let $\Lambda(z)$ be the simple lowest eigenvalue of $S+zc$ near zero,
with eigenfunction $\phi_z$ normalized by
$\langle\phi_z,\phi\rangle=M$. Then
$\Lambda(0)=\lambda_0$, $\Lambda'(0)=C/M>0$ and
$(S-\Lambda(z))\phi_z=-zc\phi_z$.
For positive fixed $\lambda$ the small positive solution of
$\Lambda(q_\epsilon^2)=\lambda_0(1+\lambda/L^2)$ satisfies

$$
q_\epsilon=\frac{\sqrt{\alpha\lambda}}L+O(L^{-3}).
\tag{20.5}
$$

This expansion is uniform on compact subsets of $(0,\infty)$.
The analytic expansion for $s_0^2$ is uniform on compact real $\lambda$
sets; no square-root expansion through zero is asserted.

Proof. Polarize (10.10), Fourier transform in $t$, and use the exact
phase $e^{-ina/2}$ from (10.11). This gives (20.3), retaining the factor
$c$ in front of $w_{tt}$. Admissible angular branches are those inherited
from smooth Cartesian annuli: the bounded natural branch for $n=0$,
and $c^{|n|/2}$ times its regular branch for $n\ne0$. A logarithm or a
negative branch on the axis creates a singularity away from the source;
hypoellipticity excludes it from a homogeneous distributional solution.

Here is an estimate covering complex frequencies in every nonzero
sector. Write $s=x+iy$, $|x|\le1$, and set
$C_b=\int c|b|^2$, $M_b=\int|b|^2$. The real part of its pairing is

$$
I_{n,y}+(1-x^2)C_b-\gamma M_b,
\quad
I_{n,y}=\int_J\{4c|b'|^2+c(y+n\tan a)^2|b|^2\}da.
\tag{20.6}
$$

Set $z_1=\operatorname{artanh}(\sin a)$. Then
$I_{n,y}=\int_{\mathbb R}\{4|b_{z_1}|^2+
(n\tanh z_1+y\operatorname{sech}z_1)^2|b|^2\}dz_1$.
Let $d>0$ have square equal to the positive root of
$X^2-(1+n^2-y^2)X-n^2y^2=0$; thus
$n^2\le d^2\le n^2+1$. With
$W_1=(d-1)\tanh z_1+(ny/d)\operatorname{sech}z_1$, multiplication gives

$$
-4\partial_{z_1}^2+(n\tanh z_1+y\operatorname{sech}z_1)^2
=(-2\partial_{z_1}+W_1)(2\partial_{z_1}+W_1)
                 +n^2-(d-1)^2.
\tag{20.7}
$$

Natural-domain approximation justifies this factorization. Hence
$I_{n,y}\ge2(\sqrt{n^2+1}-1)\int|b|^2dz_1
\ge2(\sqrt{n^2+1}-1)M_b$.
For $|n|\ge1$ this exceeds $\lambda_0M_b$, since
$2(\sqrt2-1)>2/\pi>\lambda_0$.
The adjoint pencil has $s$ replaced by $-\overline s$, so the same
estimate excludes cokernel as well as kernel and gives an
$O(|n|^{-1})$ inverse bound, uniformly in $y$ and $|x|\le1$.
A fixed small neighbourhood of $\gamma=\lambda_0$ preserves the gap.

For $n=0$, $(S-\gamma)b=s^2cb$ is a generalized selfadjoint compact
problem in $L^2(c\,da)$. At criticality its nonnegative form plus
$\int c|b|^2$ controls the original $S$ form: decompose along the simple
kernel $\phi$ and use its spectral gap. The embedding is compact by
the endpoint argument in §10. On the codimension-one space $b(0)=0$,
weighted Cauchy–Schwarz and
$c(a)\ge(2/\pi)(\pi/2-|a|)$ give
$M_b\le(\pi^2/4)\int c|b'|^2$. Thus

$$
\langle(S-\gamma)b,b\rangle-C_b
 \ge(16/\pi^2-\gamma)M_b.
\tag{20.8}
$$

Min-max puts the next generalized eigenvalue above
$1+16/\pi^2-\gamma>1$. At criticality the root zero has precisely the
two solutions stated: a further chain element would require
$(S-\lambda_0)b=c\phi$, contradicted by pairing with $\phi$.
With the stipulated scalar product the leading Laurent operator is

$$
f\longmapsto-\frac{\phi\langle f,\phi\rangle}{Cs^2}.
\tag{20.9}
$$

A branch $R^{-1+s}b$ is physically $L^2$ at zero exactly when
$\operatorname{Re}s>-1$. All remaining $L^2$ branches therefore have
real part greater than one. A reduced-inverse solution near $\phi$
gives (20.4). Bounded multiplication by $c$ similarly gives the analytic
eigenpair of $S+zc$; differentiating and pairing gives $\Lambda'(0)$.
Inverting its power series proves (20.5). These are frozen indicial
facts, not a finite-energy separation or a selected boundary condition.
$\square$

## 21. The native source-minimal and source-maximal domains

**Theorem 21.1 (one native source boundary pair with inherited walls).**
Define

$$
\mathcal D_0=\{u\in D(F):u=0\text{ on a source neighbourhood}\},\quad
S_{D,\min}=\overline{F|_{\mathcal D_0}}^{\mathrm{graph}},\quad
S_{D,\max}=S_{D,\min}^{\,*}.
\tag{21.1}
$$

These operators retain the original killed outer walls. There are real
$p,\zeta\in D(S_{D,\max})$, smooth off the source, such that

$$
\begin{gathered}
p=f_*/a_*\in D(F),\qquad
p/h=1+O(R^\gamma),\qquad
\zeta/h=\log R+O(R^\gamma),\\
D(S_{D,\max})=D(S_{D,\min})\dotplus
                         \operatorname{span}_{\mathbb C}\{p,\zeta\}.
\end{gathered}
\tag{21.2}
$$

For some fixed $0<\gamma<1$, both displayed errors are uniform over
all directions and have the corresponding rescaled-annular derivatives.
Write the unique decomposition as
$u=\mathcal A(u)p+\mathcal B(u)\zeta+u_{\min}$.
The two maps are graph-continuous, jointly onto $\mathbb C^2$, and

$$
\begin{aligned}
[u,v]&:=\langle S_{D,\max}u,v\rangle-
                    \langle u,S_{D,\max}v\rangle\\
 &=K\{\mathcal B(u)\overline{\mathcal A(v)}
                   -\mathcal A(u)\overline{\mathcal B(v)}\},\\
D(F)&=\ker\mathcal B.
\end{aligned}
\tag{21.3}
$$

The defect numbers are $(1,1)$. All other selfadjoint source realizations
with these outer walls have $\mathcal A=\kappa\mathcal B$,
$\kappa\in\mathbb R$; $\mathcal B=0$ is the remaining projective line.
The form domain of $F$ remains exactly $\mathcal Q$, strictly larger
than $\mathcal F_A$.

For general maximal elements the expansion is in angular $L^2$ and the
weighted graph topology specified below; a uniform pointwise assertion
on that whole domain is false. For maximal solutions of
$\mathcal T u=Eu$ with finite $E$, the expansion is uniform in all
angles and smooth on rescaled compact annuli. No finite-$\epsilon$
capped positive state is an element of this uncapped maximal domain.

Proof. We give the local maximal estimate, the corrected native vectors,
and the graph-domain argument before using an extension theorem.
On the cylinder $(t,\{R=1\})$ put $D_i=RZ_i$, $(Z_1,Z_2)=(U,V)$.
Let $L^2_\delta$ mean $e^{-\delta t}v\in L^2(dt\,da\,d\theta)$ and
let $X_\delta$ also control $D_iv$ and every ordered $D_iD_jv$ in
that norm. The full sphere is smooth in Cartesian coordinates; its
polar endpoints are not artificial boundaries. On overlapping unit
slabs, with a slightly larger slab on the right, one has

$$
\|v\|_{X_\delta}\le C_\delta
             (\|Pv\|_{L^2_\delta}+\|v\|_{L^2_\delta}),
\qquad P=R^3\mathcal T R^{-1}.
\tag{21.4}
$$

For clarity its horizontal second-order input can be proved directly.
For compact frozen tests, integration by parts, $T=[U,V]$, and central
Fourier transformation give

$$
\sum_{i,j}\|Z_iZ_jf\|_2^2
 =\|\Delta_Hf\|_2^2+2\|Tf\|_2^2
 \le3\|\Delta_Hf\|_2^2.
\tag{21.5}
$$

The last inequality follows from the nonnegative squared norms of
$(U\pm iV)f$ in each central Fourier fibre, which give
$\|Tf\|_2\le\|\Delta_Hf\|_2$.
Freeze a smooth SPD horizontal matrix on finitely many small patches of
a fixed annulus and absorb its small principal variation. Horizontal
interpolation absorbs first derivatives and density drift. Cutoffs give
the interior version of (21.4). To pass from smooth tests to the maximal
distributional domain, local step-two subelliptic regularity first gives
ordinary $H^1$ locally when the function and its image are $L^2$.
Friedrichs mollifier commutators are bounded $H^1\to L^2$ and tend to
zero: integrate one derivative in the commutator kernel and use the
first smooth coefficient difference. The smooth estimate then passes
weakly to the ordered horizontal second derivatives. Dilation, a bounded
overlap partition and conjugation by $e^{\delta t}$ prove (21.4).

Let $P_0=R^3(-\Delta_H-\lambda_0R^{-2})R^{-1}$. From (11.1)–(11.3)
and (16.8),

$$
P=P_0+Q_1,
\qquad Q_1=O(e^t)
\text{ in horizontal order at most two, with all slab derivatives}.
\tag{21.6}
$$

The density drift is first order of this size; the full-Green remainder
is multiplication of this size. A finite spectral energy contributes
$Ee^{2t}$ instead. These bounds are local for every fixed smooth model;
no smallness of its coefficients outside the source chart is needed.

Fourier–Laplace inversion of $P_0$ on any line
$\operatorname{Re}s=\delta\in[-1,1]\setminus\{0\}$ is bounded on
$L^2_\delta$, and (21.4) upgrades its inverse to $X_\delta$.
For $n\ne0$ use (20.6)–(20.7). For $n=0$, large
$|\operatorname{Im}s|$ controls the critical angular form plus
$\int c|b|^2$, and the remaining compact parameter interval is bounded
by invertibility and compactness. A contour shift crosses only (20.9),
producing $A\phi+Bt\phi$. First do this for compact smooth forcing;
vertical-line bounds and fast Fourier decay justify Cauchy shifts.
Then approximate in both weighted spaces. When the weights straddle
zero, exponential Cauchy–Schwarz bounds the transform and its first
derivative at zero, so the residue coefficients and the inversion pass
to the limit. Shifts not crossing zero add no term.

We must use native corrected vectors rather than $h$ and $h\log R$.
Choose $\beta$ so $\overline q_{\mathrm c}+\beta\|\cdot\|^2$ is
coercive, and let $g=\chi h\log(R/b)$ with $\chi$ supported in the
chart and one near zero. It is $L^2$ and outside $\mathcal Q$.
Its off-source residual $F_\beta=(\mathcal T+\beta)g$ is
$O(R^{-2}(1+|\log R|))$, with annular derivatives. For $f=Hw$ its
pairing is bounded by a constant times

$$
\left(\int R^{-1}H^2|w|^2d\mu\right)^{1/2}
\left(\int R^{-1}H^2(1+|\log R|)^2d\mu\right)^{1/2}.
\tag{21.7}
$$

The first factor is form-controlled by §12 and the second is finite.
Lax–Milgram gives $r\in\mathcal Q$ representing this functional.
Thus $\psi=g-r$ is $L^2$, solves $(\mathcal T+\beta)\psi=0$ off zero,
retains outer killing and is outside $\mathcal Q$.
For $r/h$ the weighted equation has forcing
$O(R^{-1}(1+|\log R|))$. The signed barriers
$M_1-D_1R^\delta b_\delta$ of (13.10), local coercivity and positive-part
comparison bound $r/h$ through zero. The zero weighted capacity in
(12.13) makes those tests legitimate. Harmonic replacement has error
$O(d(1+|\log d|))$ on $R<d$. The annular oscillation contraction of
§16 gives $r/h=A_r+O(R^\gamma)$, and interior estimates give all
rescaled derivatives. Therefore
$\psi/h=\log R+\kappa_\psi+O(R^\gamma)$.
Set $p=f_*/a_*$ and $\zeta=\psi-\kappa_\psi p$.
These are genuine native maximal vectors with (21.2).

For domain completeness, cut off above a fixed $t$ and put $v=Ru$.
Physical $u\in L^2$ means $v\in L^2_{-1}$, whereas
$\mathcal T u\in L^2$ means $Pv\in L^2_1$.
Equation (21.4) initially gives $v\in X_{-1}$, so
$P_0v\in L^2_0$ by (21.6). Choose
$0<\delta<\gamma$ and $\eta=1-\delta$. Shift from $-1$ to $-\eta$
without a pole, giving $v\in X_{-\eta}$. Now
$Q_1v\in L^2_\delta$; shifting to $\delta$ gives
$v=A\phi+Bt\phi+v_\delta$, $v_\delta\in X_\delta$.
After subtracting the actual $Ap+B\zeta$, its remainder $w$ is in
$X_\delta$, its native image is in $L^2_1$, and
$Q_1w\in L^2_{1+\delta}$. Shift once more from $\delta$ to $1$
without a pole. Thus

$$
R(u-Ap-B\zeta)\in X_1.
\tag{21.8}
$$

Remove $t<-j$ with fixed-width smooth cutoffs. The operator commutator
is $R^{-3}$ times a first-order cylinder expression; its physical $L^2$
norm is bounded by the $X_1$ tail and tends to zero. Function and image
tails also vanish. The cutoffs have finite transformed form energy by
(21.8), and their $L^2$ image identity extends to all $\mathcal Q$ tests
by form-core density. They are in $D(F)$ and vanish near the source.
This proves graph-minimality of the remainder.

The inherited outer domain follows from the adjoint definition itself.
Localize a maximal vector by a smooth function vanishing near zero and
constant outside a source annulus. Test against its products with
$D(F)$ vectors. Annular maximal regularity moves the commutator onto the
maximal vector; selfadjointness puts that localization in $D(F)$.
Further smooth localizations away from zero preserve this domain.
In particular the argument did not take the absolute adjoint of the
punctured compact core and silently discard its outer boundary data.

The inward-oriented source pairing of $p,\zeta$ has leading Wronskian
$h^2\nabla_H\log R$. Its integral is
$-(m_0/4)\int_J\int_0^{2\pi}c\phi^2=-K$.
Errors are $O(R(1+|\log R|))+O(R^\gamma(1+|\log R|))$ and vanish.
Outer pairings vanish by the inherited domain. Minimal vectors pair to
zero by graph approximation. This proves (21.3), and also
$\mathcal B(u)=[u,p]/K$, $\mathcal A(u)=-[u,\zeta]/K$.
They are graph-continuous and $p,\zeta$ realize $(1,0),(0,1)$.
The quotient dimension is two; the existing selfadjoint $F$ gives equal
defect numbers, hence each is one. Maximal isotropic lines of this
pairing are exactly the stated selfadjoint domains. Since $p\in D(F)$,
that line is $\mathcal B=0$ for $F$. Notice
$K=m_0(\pi/2)C=g_{\mathrm c}C/(4\lambda_0)$ has no $a_*^2$ factor.
$\square$

**Proposition 21.2 (trace topology and the cap-domain distinction).**
For a general maximal vector, (21.8) gives an angular $L^2$ continuous
slice representative with
$\|u_{\min}/h\|_{L^2(\{R=\mathrm{constant}\})}=o(R)$.
Consequently its total trace error in (21.2) is $O_u(R^\gamma)$ in that
angular norm. The traces do not extend continuously to the shifted form
norm on $\mathcal Q$. If $\mathcal T u=Eu$, $E$ finite, the error is
uniform over the whole sphere with all rescaled-annular derivatives;
compact-$E$ uniformity also requires bounded local solution norms.

For every fixed resolution the positive $f_{\epsilon,\lambda}$ is not
in $D(S_{D,\max})$. If a sequence of $K_{\epsilon,\lambda}$ has a
proper selfadjoint strong-resolvent limit $G$, then
$S_{D,\min}\subset G\subset S_{D,\max}$, so $G$ is one of the
realizations in Theorem 21.1. This is a restriction on an existing
limit, not an existence or selection assertion.

Proof. The fields $D_i$ and their commutator control ordinary first
cylinder derivatives. For the remainder in (21.8), $e^{-t}Ru_{\min}$
is $H^1$ in $t$ with values in angular $L^2$, and is $L^2$ in $t$.
Its slice norm tends to zero as $t\to-\infty$, proving the first claim.
For a finite-energy solution the remainder equation on rescaled annuli
has forcing $O(R^2(1+|\log R|))$ and a bounded $O(R^2)$ coefficient
multiplying that remainder. Its annular $L^2$ norm is $o(R)$.
Iterated interior estimates prove the uniform smooth expansion, reducing
$\gamma$ if necessary. The punctured form core has $\mathcal A=0$ and
is $\mathcal Q$ dense, whereas $\mathcal A(p)=1$; form continuity is
impossible. A nonzero logarithmic coefficient has infinite transformed
form energy.

There is also a direct counterexample to pointwise traces on the general
maximal domain. Choose disjoint tiny contact balls at $q_j\to0$, radii
$d_j\ll R_j=R(q_j)$, and amplitudes $a_j=h(q_j)$. In the normalized
frozen chart at $q_j$ take the smooth bump
$\eta(\log(d_j/N_j)/M_j)$, with $\eta=0$ on $(-\infty,0]$ and
$\eta=1$ on $[1,\infty)$, constant at its centre.
The identity $\Delta_H\log N_j=2|\nabla_HN_j|^2/N_j^2$ gives squared
operator cost at most $Ca_j^2/M_j$ and squared norm at most
$Ca_j^2d_j^4/M_j^2$. Smooth principal and drift errors add at most a
fixed local constant times $a_j^2d_j^2/M_j^2$; the attraction adds at
most $Ca_j^2R_j^{-4}d_j^4/M_j^2$. Choose each finite $M_j$ large enough
that its graph norm is at most $2^{-j}$. The sum is a graph limit of
punctured tests, hence minimal with both traces zero, yet its quotient
by $h$ is one at $q_j$ and zero at intervening points outside the balls.

For fixed $\epsilon$, the cap is constant near zero and its positive
state is smooth there, with $f_{\epsilon,\lambda}(o)>0$. In
$\mathcal T f_{\epsilon,\lambda}$ the leading term is
$-\lambda_0R^{-2}f_{\epsilon,\lambda}(o)$ with $O(R^{-1})$ error.
Its square has radial integral a positive multiple of $\int_0dR/R$.
It is not $L^2$, so uncapped operator traces cannot be evaluated on this
finite-resolution state. Finally, for $v\in\mathcal D_0$ the cap equals
$\Gamma$ on its support for small $\epsilon$, and
$K_{\epsilon,\lambda}v\to Fv$ in $L^2$. Passing in the resolvent
equation at a nonreal point gives $Gv=Fv$; graph closure proves the
stated inclusion. Replacing $\log R$ by $\log(R/b)$ changes the constant
trace to $\mathcal A_b=\mathcal A+\mathcal B\log b$ and therefore
$\kappa_b=\kappa+\log b$. The fixed $b$ cannot be erased from a future
selection calculation. $\square$

## 22. Frozen cap phase and the actual full-angular interior map

**Theorem 22.1 (source-regular small-frequency cap response).** For all
sufficiently small real $|z|$ there is a unique real source-regular
solution $Z_z$ of

$$
(-\Delta_H-\Lambda(z)\min(R^{-2},1))Z_z=0
\tag{22.1}
$$

with slow derivative coefficient one in the following scattering class:
for $t>0$,

$$
RZ_z=\phi_z(a)\{s_z(t)+a(z)c_z(t)\}+r_z(t,a,\theta),
\quad
s_z(t)=\frac{\sin(\sqrt z\,t)}{\sqrt z},\quad
c_z(t)=\cos(\sqrt z\,t),
\tag{22.2}
$$

where the entire power series define both expressions at $z\le0$.
The remainder has finite full cylindrical energy

$$
\int_{t>0}\left{|r|^2+
 c|r_t+\tan a\,r_\theta|^2+
 4c|r_a+r_\theta/2|^2\right}dt\,da\,d\theta<\infty.
\tag{22.3}
$$

All angular domains are inherited from Cartesian annuli.
The function is rotationally invariant as a consequence of uniqueness.
It is smooth in $R<1$ and $R>1$, is locally horizontally $W^{1,2}$
through the interface and is source-smooth. Its dependence on $z$ is
analytic in those local energy spaces, in smooth norms off $R=1$,
and at zero. Moreover

$$
Z_0=Z,\qquad a(0)=\kappa_{\rm cap}>0,\qquad Z_z(0)>0.
\tag{22.4}
$$

No global positivity is asserted when $z>0$. For a small closed real
$z$ interval and some fixed $\sigma>0$, every fixed parameter and time
derivative of $r_z$ has norm $O(e^{-\sigma t})$, for $t\ge2$, in
$H=L^2(J,c\,da)$ and
$V=\{b:\int c(|b'|^2+|b|^2)<\infty\}$ after rotational invariance.
For a compact Cartesian annulus $B_1$, the corresponding smooth bounds
on

$$
e^tZ_z(\delta_{e^t}x)-R(x)^{-1}\phi_z(a(x))
 \{s_z(t+\log R(x))+a(z)c_z(t+\log R(x))\}
\tag{22.5}
$$

hold for $t\ge T_{B_1}=\max(2,2-\log\min_{B_1}R)$.
This condition keeps the dilated annulus exterior to the literal cap;
there is no assertion of smoothness across $R=1$.

For $q>0$, $z=q^2$, define

$$
\begin{aligned}
A(q)&=\sqrt{1+q^2a(q^2)^2},&
\delta(q)&=\arctan(qa(q^2)),\quad\delta(0)=0,\\
s_{q^2}(t)+a(q^2)c_{q^2}(t)
 &=A(q)\sin(qt+\delta(q))/q.
\end{aligned}
\tag{22.6}
$$

Then
$\delta(q)=q\kappa_{\rm cap}+O(q^3)$,
$\delta'(q)=\kappa_{\rm cap}+O(q^2)$,
$\delta''(q)=O(q)$ and
$A(q)=1+\kappa_{\rm cap}^2q^2/2+O(q^4)$.
The outgoing/incoming reflection coefficient is $-e^{2i\delta(q)}$.
The exact slow-wave identity holds on $0\le t\le C_1/q$ for every
fixed $C_1$; exponential estimates retain $t\ge2$ and the exterior-annulus
restriction (22.5). Replacing only $a(q^2)$ by
$\kappa_{\rm cap}$ costs $O(q^2)$ in $RZ_z$ and $O(q^3)$ in its time
derivative on this interval; the $q$ derivative of that scalar profile
difference is $O(q)$. Replacing $\phi_{q^2}$ by $\phi$ or dropping
$A(q)$ can cost $O(q)$ in the profile. For every fixed $N_1$, taking
$t\ge(N_1/\sigma)\log(1/q)$ makes the complementary remainder $O(q^{N_1})$,
with the exterior-annulus restriction retained for Cartesian norms.
Analyticity gives $Z_z-Z=O(z)$ in the stated local topologies. The
conserved imaginary outward Green flux of a wave
$R^{-1}\phi_{q^2}B_0e^{iqt}$ in measure $m_0dq$ is
$m_0(\pi/2)qC_q|B_0|^2$, where $C_q=\int c\phi_{q^2}^2da$.
At zero frequency the unit slow derivative has Wronskian charge $m_0k$.

Proof. The join-to-middle inequality of §12 gives
$\int|b|^2\le C_1\int c(|b'|^2+|b|^2)$, so $V$ equals the accepted
angular form space as a set. Its compact embedding into $L^2(da)$
follows by the endpoint substitution $\pi/2-|a|=s^2$ and radial
Rellich compactness on a two-dimensional disk. In particular Ehrling
interpolation gives

$$
\int|b|^2da\le\eta\int c|b'|^2da+C_\eta\|b\|_H^2.
\tag{22.7}
$$

Let $T_0$ on $H$ have form $\int(4c|b'|^2+c|b|^2)$ and let
$X=D(T_0^{1/4})$. Spectral minimization of
$\int_{-\infty}^0(\|W_t\|_H^2+\|T_0^{1/2}W\|_H^2)dt$ with trace
$f$ gives $\langle T_0^{1/2}f,f\rangle$ and extension
$e^{t\sqrt{T_0}}f$. This proves the trace space, including the
characteristic polar endpoints, without assigning classical endpoint
values. Sesquilinear form maps below take values in the anti-dual of
this trace space.

The form $\int\{4c|b'|^2+(c-\gamma)|b|^2\}$ on $H$ is closed on $V$
by (22.7). At $\gamma=\lambda_0$ it is nonnegative, with simple kernel
$\phi$ and a positive complementary gap. At
$\gamma=\Lambda(z)$ its exact eigenpair on $H$ is $(-z,\phi_z)$.
Let $P_z$ be its $H$-orthogonal projection, $Q_z=1-P_z$, and
$D_z=\sqrt{A_{\Lambda(z)}|_{Q_z}}$, extended by zero on $P_z$.
The complementary gap stays positive. The maps $P_z$ and $D_z:X\to X^*$
are analytic in the appropriate trace-form sense. Indeed align $Q_z$
with $Q_0$ by the finite-rank analytic projection map close to the
identity, solve the coercive complementary half-cylinder problem, and
apply its inverse Neumann series. This argument never treats
multiplication by $c^{-1}$ as bounded on $H$.

For the interior $t<0$, writing $Z=R^{-1}W$ gives
$-cW_{tt}+(S-\gamma e^{2t})W=0$. Its normalized cylinder form is

$$
B_\gamma[W]=\int_{t<0}\int_J
 \{c|W_t|^2+4c|W_a|^2+(c-\gamma e^{2t})|W|^2\}da\,dt.
\tag{22.8}
$$

At criticality, $W=\phi v$ makes this exactly
$\int\{c\phi^2(|v_t|^2+4|v_a|^2)+
\lambda_0(1-e^{2t})\phi^2|v|^2\}$.
For $t<-1$ the last term controls mass; the fundamental theorem in $t$
controls the $c$-weighted mass on $-1<t<0$ by that mass and $v_t$.
The angular inequality (22.7) controls the remaining angular mass.
Bounded positive $\phi$ and bounded $\phi'$ therefore give coercivity
in the free cylinder norm. The perturbation in $\gamma$ is bounded in
that norm, so coercivity persists near criticality. Lax–Milgram gives a
unique finite-energy extension for every trace in $X$, and its analytic
normalized conormal $N_\gamma:X\to X^*$ satisfies
$N_{\lambda_0}\ge c_1T_0^{1/2}$ as forms.

For rotational functions the physical interior form is
$(\pi/2)(B_\gamma[W]-\|W(0)\|_H^2)$.
Thus the physical conormal is $N_\gamma-I$. This same subtraction
occurs on both sides of the interface and cancels when matching;
no new interface law is being imposed.

The operator $M_z=N_{\Lambda(z)}+D_z$ is coercive at zero and
analytically invertible for small $z$. With $\phi_z$ interpreted as the
$H$ pairing functional, set

$$
f_z=M_z^{-1}\phi_z,\qquad
a(z)=\frac{\langle f_z,\phi_z\rangle_H}{\|\phi_z\|_H^2},\qquad
r_z(t)=e^{-tD_z}Q_zf_z.
\tag{22.9}
$$

Glue its interior extension to (22.2). The trace is $f_z$ and the
exterior derivative at zero is
$\phi_z-D_zf_z=N_{\Lambda(z)}f_z$, exactly the weak matching condition.
Finite free energy at the source, its zero free capacity and bounded
interior potential remove the puncture without a delta distribution;
hypoelliptic regularity gives source smoothness. Inverse-series
dependence and interior regularity prove the local analytic claims.
At $z=0$, the accepted $Z$ has affine slow mean and bounded complementary
remainder. Spectral expansion eliminates its growing complementary
branches, hence puts it in this same matching class. Uniqueness identifies
$Z_0=Z$ and gives

$$
\kappa_{\rm cap}
=\frac{\langle M_0^{-1}\phi,\phi\rangle_H}{\|\phi\|_H^2}>0.
\tag{22.10}
$$

Analyticity and $Z(0)>0$ give the asserted positive source value.

This construction is unique in the full angular class. By (20.6)–(20.7)
and Plancherel, every nonzero $\theta$ sector has a fixed positive
uncapped cylinder gap for $\gamma$ near $\lambda_0$. The cap adds
$\gamma(1-\min(1,e^{2t}))|W|^2\ge0$. A source-regular solution in the
stated scattering class has finite cylinder energy in these sectors on
both ends. Expanding cutoffs make its equation pairing zero, while the
gap forces that sector to vanish. In the zero sector a difference with
zero slow derivative has $M_zf=0$, hence vanishes. Rotation is therefore
a conclusion about the frozen solution, with no symmetry imposed on
actual coefficients or states.

The complementary gap gives $e^{-tD_z}$ decay and smoothing after a unit
time. After projection alignment, an exponential weight with square
smaller than that gap preserves coercivity. Differentiating its inverse
series proves the same estimates for every fixed parameter derivative,
with a possibly smaller common exponent. On exterior Cartesian annuli,
interior estimates give all smooth derivatives and include the axis.
The restriction $t\ge T_{B_1}$ in (22.5) is essential. Finally (22.6)
is an exact identity; its Taylor series proves all phase estimates.
There is no growing-interval error from replacing $\sin(qt)$ by its
fixed-$t$ Taylor expansion, because no such replacement was made.
$\square$

**Corollary 22.2 (an auxiliary zero-energy nodal length).** For small
$q>0$, the first zero of $Z_{q^2}$ on every angular ray has

$$
\log R_{\rm zero}=\pi/q-\kappa_{\rm cap}
                    +O(q^2)+O(e^{-\sigma\pi/q}).
\tag{22.11}
$$

For $\mu=\sqrt{\alpha\lambda}>0$, its physical frozen nodal radius in
(20.1) is
$b\exp(-(1-\pi/\mu)L-\kappa_{\rm cap})(1+O(L^{-1}))$,
uniformly on compact positive $\lambda$ sets. At $\mu=\pi$ it tends
to $be^{-\kappa_{\rm cap}}$. This is a zero of a signed zero-energy
comparison solution, not an actual concentration radius or an equality
realization.

Proof. The first slow zero is
$t_s=\pi/q-\delta(q)/q=\pi/q-\kappa_{\rm cap}+O(q^2)$, with derivative
$-A(q)\phi_{q^2}$ bounded away from zero in every direction. The
exponential remainder gives one zero within $O(e^{-\sigma\pi/q})$.
On fixed balls $Z_{q^2}\to Z>0$. Farther out before $t_s$, the positive
slow sine is bounded below by a multiple of
$\min(t+\delta/q,t_s-t)$ off the zero neighbourhood, and dominates the
exponential remainder. Thus no earlier zero occurs. Cartesian estimates
include the polar endpoints. Apply (20.5) and multiply by
$\epsilon=be^{-L}$ to get the physical formula. $\square$

**Theorem 22.3 (actual interior response for arbitrary angular trace).**
On $B=\{R<1\}$ let $\mathcal H=W_H^{1,2}(B)$,
$\mathcal H_0=\overline{C_c^\infty(B)}^{\mathcal H}$ and
$\mathcal X=\mathcal H/\mathcal H_0$ with its quotient norm. Put

$$
\begin{gathered}
m_\epsilon(x)=m(\delta_\epsilon x),\quad
C_\epsilon(x)=C(\delta_\epsilon x),\quad
V_\epsilon(x)=\epsilon^2\Gamma_\epsilon
                 (\Psi^{-1}\delta_\epsilon x)/c_G,\\
b_{\epsilon,\gamma,\eta}[u,v]
 =\int_B\frac{m_\epsilon}{m_0}
 \{\langle C_\epsilon\nabla_Hu,\nabla_Hv\rangle
                 -\gamma V_\epsilon u\overline v-\eta u\overline v\}dq.
\end{gathered}
\tag{22.12}
$$

For $\gamma$ near $\lambda_0$ and $|\eta|$ small, the zero-trace problem
is uniformly coercive. Its harmonic extension and physical variational
conormal maps satisfy

$$
\|\mathcal H_{\epsilon,\gamma,\eta}-\mathcal H_{0,\gamma,0}\|_{
                    \mathcal X\to\mathcal H}
+\|\mathcal N_{\epsilon,\gamma,\eta}-\mathcal N_{0,\gamma,0}\|_{
                    \mathcal X\to\mathcal X^*}
 \le C_1(\epsilon+|\eta|).
\tag{22.13}
$$

For compact $B_2\Subset\{R<1/2\}$, including zero, the extension
difference has $C^j(B_2)$ norm at most
$C_{B_2,j}(\epsilon+|\eta|)\|\text{trace}\|_{\mathcal X}$.
These are estimates relative to arbitrary actual trace, with no
normalization of that trace. For the actual eigenstate set
$\gamma=\lambda_0(1+\lambda/L^2)$, $\eta=\epsilon^2E_\epsilon$.
Uniformly on compact real $\lambda$ sets,

$$
\epsilon^2E_*-\lambda_0\lambda_+/L^2
 \le\eta\le\epsilon^2T_A[\psi],
\qquad \eta\longrightarrow0,
\tag{22.14}
$$

where $\psi$ is any one fixed normalized smooth free-domain test.
Thus the actual interior error is $O(\epsilon+L^{-2})$, and is
$O(\epsilon)$ for $\lambda\le0$. Constants concern one fixed model.

Proof. Equations (11.1), (11.3) and the literal minimum give
$\|m_\epsilon/m_0-1\|_\infty+
\|C_\epsilon-I\|_\infty+\|V_\epsilon-1\|_\infty\le C_1\epsilon$
on $B$. The last potential is exactly one on $R<1/2$; on its remaining
collar the uncapped value is $R^{-2}+O(\epsilon/R)\ge1-C_1\epsilon$.
The resulting form difference is bounded by
$C_1(\epsilon+|\eta|)\|u\|_{\mathcal H}\|v\|_{\mathcal H}$ for all
angular functions. The first Dirichlet eigenvalue of $-\Delta_H$ on $B$
is attained by zero extension, local subelliptic compactness and min-max.
For its nonzero minimizer the full Hardy inequality gives

$$
\int_B|\nabla_Hv|^2\ge\lambda_0\int_BR^{-2}|v|^2
                           >\lambda_0\int_B|v|^2.
\tag{22.15}
$$

This strict gap proves the required coercivity and its stability under
the small form perturbation. Lift the quotient trace by its minimal
$\mathcal H$-norm representative, and correct in $\mathcal H_0$ using
Lax–Milgram. Subtracting the two variational equations gives the
extension bound. The definition
$\langle\mathcal Nf,g\rangle=b[\mathcal Hf,\mathcal Hg]$ then gives
the conormal bound and is independent of trace representatives.
No noncharacteristic boundary trace theorem is required.
On $B_2$ all scaled coefficients are smoothly $O(\epsilon)$ from their
frozen values and the potential is constant. Interior estimates applied
to the difference equations prove the $C^j$ bound, including zero.

On the original free domain the exact form identity is

$$
q_{\epsilon,\lambda}[f]
=\overline q_{\mathrm c}[f]+\int D_\epsilon|f|^2d\mu
 -\frac{\lambda}{L^2}g_{\mathrm c}\int\Gamma_\epsilon|f|^2d\mu.
\tag{22.16}
$$

Use $\overline q_{\mathrm c}\ge E_*\|f\|^2$,
$D_\epsilon\ge0$ and
$g_{\mathrm c}\Gamma_\epsilon\le\lambda_0\epsilon^{-2}$ for the lower
bound, and eventual positive coupling for the test upper bound.
For the unamplified pullback $u(x)=f(\Psi^{-1}\delta_\epsilon x)$,
original local energy minus $E$ times local norm is exactly
$\epsilon^2m_0 b_{\epsilon,\gamma,\epsilon^2E}[u,u]$.
The Jacobian is $\epsilon^4$ and each horizontal derivative contributes
$\epsilon^{-1}$, fixing the density and clock factors. $\square$

**Proposition 22.4 (finite energy does not stay in the slow eigenspace).**
In the frozen exterior a rotational solution $R^{-1}w(t,a)$ obeys

$$
-c(a)w_{tt}+(S-\gamma)w=Ee^{2t}w.
\tag{22.17}
$$

For $\gamma=\Lambda(z)$, no nonzero solution with $E\ne0$ remains in
$\operatorname{span}\phi_z$ on an open $t$ interval. Also
$c^{-1}\phi_z\notin L^2(c\,da)$. Nevertheless the energy term is a
bounded $V\to V^*$ form by (22.7). This refutes a scalar finite-energy
reduction, not the native classification problem.

Proof. Substitute $w=u(t)\phi_z$. It would require
$-c(a)(u''+zu)=Ee^{2t}u$. Two angles with different $c$ force
$u''+zu=0$ and then $Eu=0$. The endpoint values of $\phi_z$ are
positive, whereas $c$ has simple zeros, so
$\int\phi_z^2/c=\infty$. The bounded form claim is (22.7).
$\square$

## 23. The positive decaying profile and source-normalized actual cores

**Theorem 23.1 (the unique positive frozen decaying profile).** On the
punctured full frozen group there is a unique positive $L^2(dq)$ solution
$W_\infty$ of

$$
(-\Delta_H-\lambda_0R^{-2})W_\infty=-W_\infty,
\qquad
W_\infty/h=-\log R+\kappa_\infty+O(R^\gamma).
\tag{23.1}
$$

The logarithmic coefficient fixes its normalization. The error is uniform
in all directions, with rescaled smooth derivatives. Every nonzero
nonnegative punctured $L^2$ solution of this equation is a positive
multiple of $W_\infty$. For every smooth compact cutoff $\chi=1$ near
zero, $W_\infty+\chi h\log R$ belongs to the full frozen critical
Friedrichs form domain. This remainder property follows from positivity
and $L^2$ decay; it is not an assumed angular or extension restriction.
The solution is rotationally invariant, but $W_\infty/h$ is not a
function of $\log R$ alone. For $0<a_1<1$,
$e^{a_1R}W_\infty$ and $e^{a_1R}\nabla_HW_\infty$ are exterior $L^2$.
Its exact norm and smooth-test charge are

$$
\begin{gathered}
\int W_\infty^2dq=N=k/2,\qquad
\int hW_\infty dq=k,\\
\int h^2\nabla_H(W_\infty/h)\cdot\nabla_H\eta\,dq
 +\int hW_\infty\eta\,dq=k\eta(0),
\quad \eta\in C_c^\infty(\mathbb R^3).
\end{gathered}
\tag{23.2}
$$

The last pairing is absolutely convergent, but is not a finite-energy
point-evaluation assertion: $W_\infty/h$ has infinite transformed
energy at zero. The separate original kinetic and inverse-square costs
of $W_\infty$ also diverge there. Its normalized vector in measure
$m_0dq$ is $W_\infty/\sqrt{m_0N}$.

Proof. Let $A_F$ be the nonnegative Friedrichs operator of
$\mathcal A_0=-\Delta_H-\lambda_0R^{-2}$ on the full Cartesian punctured
core. The ground identity in §12 identifies its form with the closure
of $\mathcal E_0[v]=\int h^2|\nabla_Hv|^2dq$ in $L^2(h^2dq)$.
Choose $P=-\chi h\log R$. It is $L^2$ and
$\mathcal A_0(h\log R)=0$ off zero by (20.3). The off-source function
$F_0=(\mathcal A_0+1)P$ is $L^2$: it equals $P$ near zero, with the
other terms supported on a smooth annulus. Set
$U_0=(A_F+1)^{-1}F_0$ and $W_\infty=P-U_0$.
This constructs an $L^2$ punctured solution with the stated form
remainder, independently of a choice of selfadjoint source extension.

Write $u=U_0/h$. Near zero
$(\mathscr B_0+1)u=-\log R$, with $\mathscr B_0$ from (18.10).
The signed $R^\delta b_\delta$ barriers and local positive-part
comparison of §13 bound $u$ through the zero-capacity point.
Its harmonic replacement on $R<d$ has error at most
$Cd^2(1+|\log d|)$. The annular contraction in §16 gives
$u=u(0)+O(R^\gamma)$, with annular derivatives. This proves (23.1).
The negative part of $W_\infty$ vanishes near zero and is in the global
critical form domain. Testing its equation against that negative part
forces it to vanish. Annular positivity gives $W_\infty>0$.
Exterior Caccioppoli estimates and the Agmon identity with weight
$a_1R$, using $|\nabla_HR|^2=c\le1$, give the exterior exponential
bounds for every $a_1<1$.

Here is a positivity argument that supplies uniqueness among all
nonnegative $L^2$ solutions, rather than only among vectors already
having a prescribed form remainder. Let $F_1$ be such a nonzero
solution, $v=F_1/h$, and
$p(t)=(2\pi C)^{-1}\int c\phi^2v\,da\,d\theta$.
Annular Harnack bounds the full $v$ by $C_1p$ near zero. Integrating the
full divergence equation, with periodic $\theta$ and Cartesian axis
regularity, gives

$$
Cp''(t)=e^{2t}\int_J\phi^2\left(\frac1{2\pi}
                         \int_0^{2\pi}v\,d\theta\right)da,
\qquad 0\le p''\le C_2e^{2t}p.
\tag{23.3}
$$

The backward Volterra formula, divided by $1+|t|$, has integrable kernel
$C(1+|t|)e^{2t}$. Gronwall gives $p=O(1+|t|)$, hence the same
all-angular bound for $v$. In a small weighted ball solve
$\mathscr B_0p_0=-v$ with zero outer data. Coercivity gives existence;
comparison gives $p_0\le0$, and the preceding barriers give boundedness
and a scalar trace for $p_0$. Now $z=v-p_0>0$ is weighted harmonic and
its mean is exactly $\beta t+\alpha_1$.

For $w=z-(\beta t+\alpha_1)$, retain the entire energy in (18.12).
Writing $H_w=\int c\phi^2w^2$, the identities (18.13) give
$H_w''=8e_w\ge0$ and
$\int_t^{t+1}H_w\le C\int_{t-1}^{t+2}e_w$.
Apply their convexity argument after reversing $t$ at the negative end.
Polynomial growth excludes the exponentially growing convex
alternative; the decreasing alternative has limit zero and finite tail
energy. The annular inequality and interior estimates give $w=o(1)$ in
all directions. Thus
$v=\beta\log R+\alpha_2+o(1)$, $\beta\le0$, with
$v-\beta\log R$ in the full local weighted form domain.
If $\beta=0$, zero capacity extends the equation through zero, and
exterior Caccioppoli puts $F_1$ in the global Friedrichs form domain.
Its eigenvalue $-1$ would contradict $A_F\ge0$.
Hence $\beta<0$. The difference $F_1-(-\beta)W_\infty$ is in that
form domain globally, is killed by $A_F+1$, and is zero.
This proves the claimed uniqueness; it makes no uniqueness claim for
sign-changing maximal-domain functions.

Rotation preserves the problem and logarithmic normalization, so
uniqueness gives rotational invariance. A quotient depending only on
$t$ would require $c(a)v_{tt}=e^{2t}v$ at every angle, impossible for
nonzero $v$ because $c$ is nonconstant. The angular rearrangement is
therefore real even though no $\theta$ dependence remains.

For the constants, put $W_j(q)=jW_\infty(\delta_jq)$, $j>0$.
Its energy is $-j^2$ and its constant trace is
$\kappa_\infty-\log j$. The full Green identity, with the source
orientation of §21 and exponential exterior decay, is

$$
(l^2-j^2)\int W_jW_l\,dq=k\log(l/j).
\tag{23.4}
$$

Let $l\to j$ using strong $L^2$ continuity of dilation to obtain
$\int W_j^2=k/(2j^2)$. The outward small-sphere flux of
$h^2\nabla_H(W_\infty/h)$ tends to $-k$. Integrating its divergence
$hW_\infty$ between two spheres and letting the exterior sphere tend
to infinity gives the second integral in (23.2). The same computation
against a smooth compact $\eta$ gives the charge formula. This uses
$\pi C/2$, the full angle and the polar factor $1/4$; no scalar Bessel
normalization is substituted. $\square$

**Theorem 23.2 (actual cap shape for every fixed real detuning).** Define
the actual source amplitude and linear charge by

$$
A_\epsilon=\frac{\epsilon f_\epsilon(o)}{Z(0)}>0,
\qquad Q_\epsilon=\int D_\epsilon f_*f_\epsilon\,d\mu.
\tag{23.5}
$$

For every fixed real $\lambda$,

$$
\frac{\epsilon f_\epsilon(\Psi^{-1}\delta_\epsilon q)}{A_\epsilon}
 \longrightarrow Z(q)
\tag{23.6}
$$

locally uniformly and strongly in $W_H^{1,2}$, including zero and the
cap interface; convergence is smooth on compact sets off $R=1$.
Writing $I=I_{\rm cap}$ from (18.15), one has

$$
\begin{aligned}
\frac{V_{\rm raw}[f_\epsilon]-V_{\rm cap}[f_\epsilon]}{A_\epsilon^2}
 &\longrightarrow I/(2\pi),\\
\frac{\int_{\mathcal C_\epsilon}\Gamma f_\epsilon^2d\mu}{A_\epsilon^2}
 &\longrightarrow\frac1{2\pi}\int_{R<1}R^{-2}Z^2dq,\\
\frac{\int_{\mathcal C_\epsilon}\Gamma_\epsilon f_\epsilon^2d\mu}
     {A_\epsilon^2}
 &\longrightarrow\frac1{2\pi}\int_{R<1}Z^2dq,\\
Q_\epsilon/A_\epsilon&\longrightarrow a_*m_0k.
\end{aligned}
\tag{23.7}
$$

All these limits are uniform on compact real $\lambda$ sets for one
fixed model. They give no standalone rate for $A_\epsilon$.
At $\lambda=0$ the sharper normalization is already supplied by §18.

Proof. Equation (22.14) gives $\epsilon^2E_\epsilon\to0$ uniformly on
such parameter sets. After dilation, divide the positive state by its
source value. Bounded-potential Harnack on every fixed rescaled ball
bounds these ratios above and below, and gives compactness through
zero. The scaled coefficients and literal capped potential converge to
(18.1). Every subsequential limit is positive, entire, source-regular
and has its prescribed value at zero. The all-angular uniqueness proof
of §18 identifies it as $Z/Z(0)$. Subtracting the weak equations and
testing with a cutoff times the difference gives strong local
horizontal energy convergence, including through $R=1$. Interior
estimates give smooth convergence only away from that interface.

For the three quadratic integrals use (14.2) and the exact scaled
measure $\epsilon^4m(\delta_\epsilon q)dq$.
The state square contributes $A_\epsilon^2\epsilon^{-2}$ and the
multiplier contributes $c_G\epsilon^{-2}$; the coefficient is
$m_0c_G=1/(2\pi)$. Bounded core ratios and integrability of $R^{-2}$
against $R^3dR$ justify dominated convergence through zero and the
moving interface. For the linear charge the four factors are
$\lambda_0\epsilon^{-2}(R^{-2}-1)$,
$a_*\epsilon^{-1}h$, $A_\epsilon\epsilon^{-1}Z$, and
$m_0\epsilon^4dq$. The dominating kernel is $O(R^{-3})$, still
integrable. Equation (18.5) gives its constant $a_*m_0k$.
The same subsequence argument with varying parameters in a fixed compact
set proves the asserted uniformity. No trace-amplitude estimate has been
assumed or extracted from this local normalization. $\square$

**Proposition 23.3 (cap dilation and actual core kinetic cost).** The
accepted profile also satisfies

$$
\lambda_0\int_{R<1}Z^2dq=N=k/2,
\qquad
\frac{T_A[f_\epsilon;\mathcal C_\epsilon]}{m_0A_\epsilon^2}
 \longrightarrow\int_{R<1}|\nabla_HZ|^2dq.
\tag{23.8}
$$

The second statement has the compact-real-$\lambda$ uniformity of
Theorem 23.2. These are identities for the same soft cap, not for a
Dirichlet hole.

Proof. For $a_2>0$ put
$Z_{a_2}(q)=a_2^{-1}Z(\delta_{1/a_2}q)$ and
$V_{a_2}=\min(R^{-2},a_2^{-2})$.
The quotient at infinity is $\log R+\kappa_{\rm cap}-\log a_2$.
Green's identity gives the exact compactly supported integral

$$
\lambda_0\int(V_{a_2}-V_{b_2})Z_{a_2}Z_{b_2}\,dq
                              =k\log(b_2/a_2).
\tag{23.9}
$$

Source regularity removes the inner boundary. At infinity the weighted
means of the angular remainders are exactly zero, so their cross terms
with the affine mean vanish. The remainder-remainder flux tends to zero
by its annular energy decay from §22. Thus (23.9) does not differentiate
an unspecified asymptotic remainder. Divide by $b_2-a_2$ and let
$b_2\to a_2$. Local dilation continuity and bounded compactly supported
potential difference quotients give
$2\lambda_0a_2^{-3}\int_{R<a_2}Z_{a_2}^2=k/a_2$.
Dilation proves the first identity in (23.8).
The strong local horizontal convergence in (23.6), smooth coefficient
convergence and the changed-set sandwich (14.2) prove the second.
Strong energy convergence also controls the moving collar at $R=1$.
$\square$

## 24. Actual supercritical concentration and separate resources

**Theorem 24.1 (sharp actual ground laws above the first threshold).**
Fix any one model of Definition 20.1 and $\lambda>\lambda_D$.
Let $q=q_\epsilon$ be (20.5), $\mu=\sqrt{\alpha\lambda}>\pi$, and put
$\kappa_\Sigma=\kappa_{\rm cap}+\kappa_\infty$.
Then $E_\epsilon\to-\infty$. For
$s=s_\epsilon=(-E_\epsilon)^{-1/2}$,

$$
\begin{aligned}
\log(s/\epsilon)&=\pi/q-\kappa_\Sigma+o(1),\\
-E_\epsilon
 &=\epsilon^{-2}\exp(-2\pi/q+2\kappa_\Sigma)(1+o(1))\\
 &=e^{2\kappa_\Sigma}b^{-2}
                \exp(2(1-\pi/\mu)L)(1+o(1))\\
 &=e^{2\kappa_\Sigma}b^{-2\pi/\mu}
                \epsilon^{-2+2\pi/\mu}(1+o(1)).
\end{aligned}
\tag{24.1}
$$

In the injective concentration chart, extend by zero outside that chart
and set
$G_\epsilon(q)=s^2\sqrt{m_0}f_\epsilon(\Psi^{-1}\delta_sq)$.
Then

$$
\begin{gathered}
G_\epsilon\longrightarrow W_\infty/\sqrt N
                         \quad\hbox{strongly in }L^2(dq),\\
s\sqrt{m_0N}A_\epsilon\longrightarrow1,\qquad
sQ_\epsilon\longrightarrow a_*\sqrt{m_0}\,k/\sqrt N.
\end{gathered}
\tag{24.2}
$$

Profile convergence is also strong locally in horizontal $W^{1,2}$ off
zero and smooth on punctured compact Cartesian sets, including the axis.
The original mass measures tend to $\delta_o$ and the original normalized
vectors tend weakly to zero in $L^2(\mu)$. Horizontal source-coordinate
scale is $s$, adapted central scale $s^2$.
At the cap scale,
$\epsilon s\sqrt{m_0N}f_\epsilon(\Psi^{-1}\delta_\epsilon q)\to Z(q)$
in all the local senses of Theorem 23.2, including its source value.

The actual total resources satisfy

$$
\begin{aligned}
s^2q^3V_{\rm raw}[f_\epsilon],\quad
s^2q^3V_{\rm cap}[f_\epsilon]&\longrightarrow\frac{M}{2m_0C},\\
s^2q^3T_A[f_\epsilon]&\longrightarrow\pi\alpha.
\end{aligned}
\tag{24.3}
$$

Equivalently, after division by $|E_\epsilon|L^3$, the two attractions
have limit $M/(2m_0C\mu^3)$ and kinetic energy has limit
$\pi\alpha/\mu^3$. In addition,

$$
\begin{aligned}
s^2(V_{\rm raw}-V_{\rm cap})[f_\epsilon]
 &\longrightarrow\frac I{2\pi m_0N},\\
s^2\int_{\mathcal C_\epsilon}\Gamma f_\epsilon^2d\mu
 &\longrightarrow\frac1{2\pi m_0N}\int_{R<1}R^{-2}Z^2dq,\\
s^2\int_{\mathcal C_\epsilon}\Gamma_\epsilon f_\epsilon^2d\mu
 &\longrightarrow\frac1{2\pi m_0N}\int_{R<1}Z^2dq,\\
s^2g_{\mathrm c}\int_{\mathcal C_\epsilon}
                       \Gamma_\epsilon f_\epsilon^2d\mu&\longrightarrow1,\\
s^2T_A[f_\epsilon;\mathcal C_\epsilon]
 &\longrightarrow N^{-1}\int_{R<1}|\nabla_HZ|^2dq.
\end{aligned}
\tag{24.4}
$$

Replacing $g_{\mathrm c}$ by $g_{\epsilon,\lambda}$ in the fourth line
does not change its limit. All statements are uniform for $\lambda$ in
compact subsets of $(\lambda_D,\infty)$ for this fixed model, with fixed
$b$. They assert neither an equality limit nor a resolvent theorem for
the remaining spectral subspace.

Proof. First derive collapse from an original-domain test. Choose
$\pi/\mu<\sigma_1<1$ and on
$2\epsilon<R<r_1=2\epsilon e^{\sigma_1L}$ use
$h\sin(\pi\log(R/(2\epsilon))/(\sigma_1L))$, extended by zero.
It belongs to $\mathcal F_A$ and is outside the actual cap for small
$\epsilon$ by (14.2). The exact frozen numerator is

$$
\frac{m_0k}{2L}(\pi^2/\sigma_1-\alpha\lambda\sigma_1)<0.
\tag{24.5}
$$

In the $h$ transform, the principal error integrates
$R|p'|^2dt$ and the critical full-Green remainder integrates $p^2dR$;
both are $O(r_1/L^2)$. The squared norm is comparable above and below
to $r_1^2/L^2$. Hence $E_\epsilon\le-c_{\sigma_1}L/r_1^2\to-\infty$.
Together with (22.14), this gives $s\to0$ and
$r=\epsilon/s\to0$. A common strict $\sigma_1$ margin works on each
compact supercritical parameter set.

We next prove concentration independently of the multiplicative energy
constant. In concentration coordinates write $m_s=m(\delta_s q)$,
$C_s=C(\delta_s q)$, and $h_q=R^{-1}\phi_{q^2}(a)$.
On $2r<R<r_0$ the cap is absent. Put $v=G_\epsilon/h_q$ and define

$$
\begin{gathered}
C_q=\int_Jc\phi_{q^2}^2da,\quad k_q=\pi C_q/2,\quad
p(t)=\frac1{2\pi C_q}\int c\phi_{q^2}^2v\,da\,d\theta,\\
J(t)=\int_{R=e^t}\!m_sh_q^2C_s\nabla_Hv\cdot n_H\,dS,
\qquad j(t)=J(t)/(m_0k_q).
\end{gathered}
\tag{24.6}
$$

The flux integral means the horizontal divergence flux on that Cartesian
gauge sphere. The actual equation, keeping its entire angular response,
gives

$$
p'=j+e_1,\qquad j'=-q^2p+e_2,\qquad
|e_1|\le C_1se^tp,\quad
|e_2|\le C_1(e^{2t}+se^t)p.
\tag{24.7}
$$

Here are its error estimates. The exact frozen residual of $h_q$ is
$h_q^{-1}(-\Delta_H-\gamma R^{-2})h_q=-q^2cR^{-2}$, with
$\gamma=\lambda_0(1+\lambda/L^2)$.
The native coefficient, density and full-Green residual is $O(s/R)$.
The frozen flux is exactly $m_0k_qp'$; its $\theta$ cross derivative
integrates to zero. Since $m_sC_s/m_0-I=O(sR)$ and annular
Harnack/interior estimates give $|\nabla_Hv|\le C_1p/R$, its actual
flux differs by $O(sRp)$. Integrating the full divergence equation
gives the second equation. Its finite-energy term is the complete
positive angular integral
$e^{2t}\int\phi_{q^2}^2v/(2\pi C_q)$, bounded by $C_1e^{2t}p$ by
Harnack. The density correction to $q^2p$ is absorbed by $C_1sRp$.
Cartesian regularity justifies all integrations at the collapsed axes.
In particular (24.7) is an estimate on the full state, not the false
finite-energy separation excluded in Proposition 22.4.

At a fixed small $r_0$, local $L^2$ normalization and interior estimates
bound $p,j$. Integrate (24.7) backward with its oscillator matrix. For
$u=\log(r_0/R)$, $|\sin(qx)|/q\le x$ gives

$$
p(u)\le C_1(1+u)+\int_0^u
                  \{b_1(v)+(u-v)a_1(v)\}p(v)dv,
\tag{24.8}
$$

where $a_1(v)\le C_1(r_0^2e^{-2v}+sr_0e^{-v})$ and
$b_1(v)\le C_1sr_0e^{-v}$. Divide by $1+u$ and apply Gronwall to
its integrable kernel. Thus $p\le C_2(1+u)$ down to $R=2r$.
Harnack gives the same bound on $v$ over each full sphere. Inside the
cap, its own scale Harnack gives
$G_\epsilon\le C_2r^{-1}(1+|\log r|)$. Consequently the inner mass is
bounded by

$$
C_2\int_0^d R(1+|\log R|)^2dR
                  +C_2r^2(1+|\log r|)^2.
\tag{24.9}
$$

It vanishes in the iterated limits, so no cap or angular sector hides
ordinary norm.

For the outer end use an actual-domain quadratic IMS partition at
original radius $K_1s$. The scaled outer potential is at most
$C_3/K_1^2+C_3s^2$, its kinetic form is nonnegative, and the inner
localized form is at least $-1$ times its norm by the actual global
minimum. The scaled IMS error is $C_3/K_1^2$. Hence the outer mass is
at most $C_4/(K_1^2-C_4)$ for large $K_1$, including the complement of
the source chart. Punctured-annulus compactness, (24.9), and this outer
tightness give a strong global $L^2(dq)$ limit of norm one. Its equation
is $\mathcal A_0G=-G$ and it is positive. Theorem 23.1 identifies it as
$W_\infty/\sqrt N$. Difference equations give the claimed local energy
and smooth convergence. Both tightness estimates prove the original
mass and weak-vector assertions as well.

For constant-level matching set $D=\log(s/\epsilon)$ and fix a large
$T_1$. The middle interval is $-D+T_1<t<-T_1$.
The outer profile gives
$(p,j)(-T_1)\to(p_\infty,p_\infty')(-T_1)/\sqrt N$.
Integrating (23.3) for the already normalized $W_\infty$ improves its
mean bounds to

$$
p_\infty(-T_1)=T_1+\kappa_\infty+O(e^{-2T_1}(1+T_1)),\quad
p_\infty'(-T_1)=-1+O(e^{-2T_1}(1+T_1)).
\tag{24.10}
$$

No bare trace remainder was differentiated. The inner core theorem and
the exact affine cap flux (18.11) give
$(p,j)(-D+T_1)/a_\epsilon\to(T_1+\kappa_{\rm cap},1)$, with
$a_\epsilon=s\sqrt{m_0}A_\epsilon$. At this stage $T_1$ stays fixed;
no cap convergence rate on a growing ball is used.

Set $X=j$, $Y=qp$, $C_0=(X^2+Y^2)^{1/2}$ and
$\vartheta=\operatorname{atan2}(Y,X)$. Positivity makes
$0<\vartheta<\pi$ throughout the interval. The exact identities are

$$
C_0'=\frac{je_2+q^2pe_1}{C_0},\qquad
\vartheta'=q+q\frac{je_1-pe_2}{C_0^2}.
\tag{24.11}
$$

Backward estimate (24.8) also gives $p\le C(1+u)$ with $u=-t$.
Variation of the freely rotating $(X,Y)$ vector bounds its norm change
by $C\int_{T_1}^\infty(e^{-2u}+se^{-u})(1+u)du$.
Together with (24.10) this bounds $C_0$ below independently of
$\epsilon$, and its limiting deviation from $1/\sqrt N$ tends to zero
as $T_1\to\infty$. More decisively,

$$
\frac{|\vartheta_{\rm out}-\vartheta_{\rm in}-q(D-2T_1)|}{q}
 \le C\int_{T_1}^\infty(e^{-2u}+se^{-u})(1+u)^2du.
\tag{24.12}
$$

This is the phase error divided by $q$, required for a multiplicative
energy equivalent. An undivided $o(1)$ would not suffice.
At the inner end $\vartheta_{\rm in}/q\to T_1+\kappa_{\rm cap}$;
at the outer end
$(\pi-\vartheta_{\rm out})/q\to T_1+\kappa_\infty+o_{T_1}(1)$.
First let $\epsilon\to0$, then $T_1\to\infty$ in (24.12).
This proves $D=\pi/q-\kappa_\Sigma+o(1)$.
Norm comparison of the rotating vector at the two ends gives
$a_\epsilon\to1/\sqrt N$. The positive projection stays in the upper
half-plane and selects the first half-wave $\pi$. This proves (24.1)
and the amplitude in (24.2); Theorem 23.2 gives its charge and cap form.

It remains to verify resources for the full angular state. On the middle
annulus put $w=v-p$ with zero $c\phi_{q^2}^2$ slice mean. The exact
orthogonal identity (17.9) persists with $\phi_{q^2}$ and $k_q$;
the enlarged-annulus inequality (17.10) is uniform for small $q$.
Testing the full actual equation, absorbing its small coefficient errors,
gives

$$
\mathcal E_{0,q}[v;\mathrm{middle}]
 \le C_{T_1}+Cq^2\int\phi_{q^2}^2v^2
                  +Cs\int e^t\phi_{q^2}^2v^2=O_{T_1}(q^{-1}).
\tag{24.13}
$$

Endpoint boundary terms and slightly enlarged fixed collars are
$O_{T_1}(1)$ by the matched cap amplitude and outer profile.
The logarithmic bound and $D=\pi/q+O(1)$ give
$\int\phi_{q^2}^2v^2=O(q^{-3})$; its $e^t$-weighted integral is bounded.
Orthogonality and the summed Poincaré estimate therefore give the full
remainder bound

$$
\int\phi_{q^2}^2w^2=O_{T_1}(q^{-1}),\qquad
\int p^2dt=\frac\pi{2Nq^3}(1+o(1)).
\tag{24.14}
$$

The second equality follows from the exact phase and norm comparison:
after the fixed-$T_1$, then large-$T_1$ limits the amplitude is
$1/\sqrt N$ and $q$ times the interval length tends to $\pi$.
The attraction's unweighted angular cross term is $O(q^{-2})$ by
Cauchy–Schwarz, and the squared remainder is $O(q^{-1})$.
Thus the entire state, not just its mean, obeys

$$
\int R^{-2}G_\epsilon^2dq
                  =\frac{\pi^2M}{4Nq^3}(1+o(1)).
\tag{24.15}
$$

The inner cap and fixed near-cap collar contribute $O_{T_1}(1)$ to
this integral by their now matched amplitude. The outer part is
$O_{T_1}(1)$ by normalization. Also
$\int R^{-1}G_\epsilon^2dq=O(1)$, using the logarithmic bound.
The native density and full-Green errors consequently contribute only
$O(s^{-1})$ to attraction, below $s^{-2}q^{-3}$.
Multiplication by $c_Gs^{-2}$ proves the raw constant
$\pi M/(8m_0N)=M/(2m_0C)$. The direct cap differences from Theorem 23.2
are $O(s^{-2})$, so the capped constant agrees. Finally
$T_A=E_\epsilon+g_{\epsilon,\lambda}V_{\rm cap}$ proves the kinetic
constant $\pi\alpha$. No derivative of an energy remainder was taken.
Equations (23.7)–(23.8) and the amplitude prove all of (24.4).
All estimates admit parameter subsequences in a compact supercritical
set with a common collapse margin; this proves the stated uniformity.
$\square$

**Proposition 24.2 (boundedness at and below the first threshold).** For
every fixed real $\lambda\le\lambda_D$, the actual ground energies are
bounded below as $\epsilon\downarrow0$. Together with the fixed test
upper bound they remain bounded. At $\lambda=\lambda_D$ this asserts
boundedness, not an identified energy limit, state or realization.

Proof. For $\lambda\le0$, (22.16) gives $E_\epsilon\ge E_*$.
For $0<\lambda\le\lambda_D$, failure of a lower bound would give a
sequence $E_\epsilon\to-\infty$. Its cap bound still gives
$\epsilon^2|E_\epsilon|\to0$. The concentration compactness, positive
profile identification and phase argument above require only these
collapse assumptions and $q\to0$. The supercritical trial was used only
to obtain collapse initially. They therefore imply on this sequence

$$
\log(s/b)=(\pi/\sqrt{\alpha\lambda}-1)L-\kappa_\Sigma+o(1).
\tag{24.16}
$$

Its right side is bounded below when $\lambda\le\lambda_D$, including
equality. Its left side tends to $-\infty$ because $s\to0$, a
contradiction. Finite total energy here supplies no bounded-resource
conclusion. $\square$

## 25. Higher-order actual laws at the vanishing leading coefficient

**Definition 25.1 (normalized finite part and angular curvature).** Let
$\bar c=C/M$ and use the reduced inverse of $S-\lambda_0$ on
$\phi^\perp$ in $L^2(da)$. Put

$$
\begin{gathered}
v_{\rm ang}=(c-\bar c)\phi,\qquad
Q_{\rm ang}=\langle(S-\lambda_0)^{-1}_{\phi^\perp}v_{\rm ang},
                                                v_{\rm ang}\rangle,\\
B_3=\frac{\mathsf K\nu^4Q_{\rm ang}}{2C},\\
R_b=\lim_{d\downarrow0}\left\{
 g_{\mathrm c}\int_{\Omega\setminus\Psi^{-1}\{R<d\}}
                 \Gamma f_*^2d\mu-\mathsf D\log(b/d)\right\},
\qquad S_b=R_b+\mathsf D\kappa_{\rm cap}.
\end{gathered}
\tag{25.1}
$$

These use the globally normalized $f_*$, its actual trace $a_*$ and the
full killed Green field. In particular their normalization is not a
local choice of eigenfunction size.

**Theorem 25.2 (actual energy, state and resources at $\lambda_Z$).**
For every fixed model and fixed admissible $b$, the finite part exists,
$Q_{\rm ang}>0$, $B_3>0$, and

$$
E_{\epsilon,\lambda_Z}-E_*
 =-\frac{\lambda_ZS_b}{L^2}-\frac{B_3}{L^3}+o(L^{-3}).
\tag{25.2}
$$

This is an absolute remainder for that fixed model and $b$; it is not
a differentiated expansion. There is a positive normalized matched
$v_L\in\mathcal F_A$ such that, for a fixed sufficiently large $\beta$,

$$
\|f_{\epsilon,\lambda_Z}-v_L\|_{a_\epsilon}=O(L^{-2}),
\quad a_\epsilon=q_{\epsilon,\lambda_Z}+\beta\|\cdot\|_2^2,
\qquad \|f_{\epsilon,\lambda_Z}-f_*\|_2=O(L^{-2}).
\tag{25.3}
$$

No $a_\epsilon$ norm of $f_*$ is taken: $f_*\notin\mathcal F_A$.
For these actual states,

$$
\begin{aligned}
g_{\mathrm c}V_{\rm cap}&=\mathsf D L/2+S_b+o(1),\\
g_{\mathrm c}V_{\rm raw}&=\mathsf D L/2+S_b+o(1),\\
T_A&=\mathsf D L/2+S_b+E_*+o(1),\\
L^2(V_{\rm raw}-V_{\rm cap})
 &\longrightarrow\frac{a_*^2\nu^2I}{2\pi}.
\end{aligned}
\tag{25.4}
$$

The reference rule is
$S_{b'}=S_b-\mathsf D\log(b'/b)$. Hence
$b_{\rm bal}=b\exp(S_b/\mathsf D)$ is reference-independent, but need
not lie in the admissible chart interval. If the fixed admissible
$b\ne b_{\rm bal}$, then

$$
E_{\epsilon,\lambda_Z}-E_*
 \sim\frac{\lambda_Z\mathsf D\log(b/b_{\rm bal})}{L^2}.
\tag{25.5}
$$

If $b=b_{\rm bal}$ is admissible, the equivalent is $-B_3/L^3$.
There is no further cancellation at this order. Even in that case
$\mathsf D>0$ and the separate resources in (25.4) diverge linearly.
The higher-order statements have fixed-model, fixed-$b$ scope only.

Proof. We establish quantitative form control before transferring the
Rayleigh expansion to the actual spectral minimum.
For $f=f_*u\in\mathcal F_A$, let $d\nu_*=f_*^2d\mu$ and define

$$
\begin{aligned}
B_\epsilon[u]&=\mathscr A[u]+\int D_\epsilon|u|^2d\nu_*,\\
\mathcal W_\epsilon[u]&=g_{\mathrm c}\int\Gamma_\epsilon|u|^2d\nu_*.
\end{aligned}
\tag{25.6}
$$

The exact identity, valid with finite terms on this original domain, is

$$
q_{\epsilon,\lambda}[f]-E_*\|f\|_2^2
            =B_\epsilon[u]-\lambda\mathcal W_\epsilon[u]/L^2.
\tag{25.7}
$$

The accepted source trace and its derivatives give
$f_*^2mC=a_*^2m_0h^2(I+O(R^\gamma))$.
The signed difference between
$g_{\mathrm c}\Gamma f_*^2d\mu$ and
$a_*^2m_0\lambda_0R^{-2}h^2dq$ is bounded by
$C_1R^\gamma\phi^2dt\,da\,d\theta$.
Its integral converges at zero, proving existence of $R_b$ and its
reference rule. This error is also bounded in the critical form dual:
for every $p_1>0$, integration by parts as in (12.11) gives
$\int e^{p_1t}F^2\le4b^{p_1}p_1^{-2}\int|F_t|^2$ for locally
supported tests. Combine this with (12.9)–(12.10) and a fixed cutoff to
obtain, for arbitrary angular $u$,

$$
\int_{R<b}R^\gamma\phi^2|u|^2dt\,da\,d\theta
          \le C_2(\mathscr A[u]+\|f_*u\|_2^2).
\tag{25.8}
$$

The literal cap-interface errors are confined to
$R=\epsilon(1+O(\epsilon))$ and are negligible at the polynomial orders
below.

We need a uniform actual spectral gap near $\lambda_Z$.
Let $p(t)$ be the $c\phi^2$ mean of $u$, and $w=u-p$.
The positive deficit on $R<\epsilon/2$, adjacent fixed-width collars,
(17.9) and (17.10) give
$|p(\log\epsilon)|^2\le C_3B_\epsilon[u]$ and
$\mathcal W_\epsilon[u;R<\epsilon]\le C_3B_\epsilon[u]$.
At a fixed small $d$, its outer trace is bounded by
$C_d(\mathscr A[u]+\|f\|^2)$. On an interval of length $\ell$, subtract
the affine endpoint interpolant and apply Dirichlet Poincaré:

$$
\int|p|^2\le(1+\eta)\frac{\ell^2}{\pi^2}\int|p'|^2
      +C_\eta\ell(|p(\mathrm{left})|^2+|p(\mathrm{right})|^2).
\tag{25.9}
$$

The full angular remainder is controlled by summed (17.10).
The ratio of the leading potential and derivative coefficients is
$\mathsf D/\mathsf K=\alpha$. Split first at a fixed $d$, then reduce
$d$ to control the coefficient error. Terms $CLB_\epsilon$ are absorbed
in $\eta L^2B_\epsilon$. This proves, for every $\eta>0$,

$$
\mathcal W_\epsilon[u]
 \le(\alpha/\pi^2+\eta)L^2B_\epsilon[u]
                           +C_\eta L\|f\|_2^2.
\tag{25.10}
$$

Thus, on any fixed compact $\lambda$ set strictly below $\lambda_D$,
(25.7) is bounded below by
$c_1B_\epsilon[u]-C_1L^{-1}\|f\|^2$.
The shifted form near $\lambda_Z=\lambda_D/4$ is consequently uniformly
equivalent to $B_\epsilon+\|f\|^2$. Its bounded sublevels are bounded
in the accepted compact critical completion.
Pairings against every fixed punctured-core test converge to the
critical pairing: its cap defect is zero and its detuning tends to zero
as a bounded multiplier on that support. For the lower form inequality,
apply positivity of the shifted form to $f-z$, pass to the limit for
every fixed core $z$, and take the supremum over that dense core.
The supremum is exactly the shifted completed critical form.
Diagonal core approximation gives recovery. Compact min-max therefore
gives convergence of the first two actual eigenvalues to those of $F$.
Simplicity from (15.6) gives a uniformly positive first gap near
$\lambda_Z$. The same estimates and gap argument are uniform on fixed
compact subthreshold parameter sets; no equality gap is asserted.

For the angular curvature, analytic perturbation from §20 gives

$$
\dot\phi_0=-(S-\lambda_0)^{-1}_{\phi^\perp}(c-\bar c)\phi,
\qquad \Lambda''(0)=-2Q_{\rm ang}/M<0.
\tag{25.11}
$$

Strictness holds because $c$ is nonconstant, $\phi>0$, and the reduced
inverse is strictly positive. The regular endpoint branch stays smooth.
For $\lambda=\lambda_Z$ the root $q=q_L$ therefore has expansion

$$
q=\nu/L+\frac{Q_{\rm ang}\nu^3}{2CL^3}+O(L^{-5}).
\tag{25.12}
$$

We use the exponential core tail proved in Theorem 22.1. More explicitly,
let $z_{\rm cap}=Z/h$ and $y=\log R$. For $y>0$ its exact mean is
$y+\kappa_{\rm cap}$; write its zero-mean remainder as $w$.
It is rotationally invariant. The weighted Poincaré inequality
$\int c\phi^2w^2\le C_4\int c\phi^2w_a^2$ follows by integrating the
resistance bound for $|w(a)-w(b)|^2$ against both weights; its logarithmic
endpoint singularities are integrable. Hence for
$H_w=\int c\phi^2w^2$ the equation gives
$H_w''=2\int c\phi^2w_y^2+8\int c\phi^2w_a^2\ge\sigma_0^2H_w$.
Its polynomial growth excludes the growing solution, so $H_w$ and
$-H_w'$ decay exponentially. Annular estimates give all rescaled smooth
derivatives. With
$B_0[v]=\mathcal E_0[v]+\int\lambda_0(R^{-2}-1)_+h^2|v|^2dq$,
the exact core flux is

$$
B_0[z_{\rm cap};R<e^T]
 =k(T+\kappa_{\rm cap})+\frac\pi2\int c\phi^2w(T)w_y(T)da
 =k(T+\kappa_{\rm cap})+O(e^{-\sigma T}).
\tag{25.13}
$$

Source regularity makes the inner flux zero. Its capped attraction
through $e^T$ is $O((1+T)^3)$. These are quantitative growing-annulus
bounds, stronger than a bare finite part.

Set $\theta_L=q(L+\kappa_{\rm cap})$,
$c_L=q/\sin\theta_L$ and
$P_L(y)=\sin(q(y+\kappa_{\rm cap}))/\sin\theta_L$.
Take $T=A_0\log L$ with $A_0>4/\sigma$, and
$r_L=\epsilon e^{T+1}$. Define a quotient $u_L$ in the original chart
by $c_Lz_{\rm cap}(\delta_{1/\epsilon}q_{\rm chart})$ below
$R=\epsilon e^T$, by $(\phi_{q^2}/\phi)P_L(\log(R/\epsilon))$ above
$R=\epsilon e^{T+1}$ and below $b$, and join them with a fixed smooth
cutoff of $y-T$. Extend a fixed distance past $b$ and cut the quotient
smoothly to one. At the inner join the discrepancy, including fixed
annular derivatives, is

$$
O(qe^{-\sigma T}+q^3(1+T)^3).
\tag{25.14}
$$

At the outer collar it is $O(q^2)$ from one, with derivatives.
On the middle annulus, $x=\log(b/R)$ gives
$|P_L-1|\le Cq^2(1+x)^2$,
$|P_L'|\le Cq^2(1+x)$, and
$\phi_{q^2}/\phi-1=O(q^2)$ with angular derivatives.
Near zero the actual product $t_L=f_*u_L$ is
$c_L\epsilon^{-1}(f_*/h)Z(\delta_{1/\epsilon}q_{\rm chart})$.
Its original horizontal energy is finite because $Z$ is source-smooth
and $|X(f_*/h)|\le CR^{\gamma-1}$. Free zero-capacity cutoffs remove
the point; localization retains the actual height killing. Thus
$t_L\in\mathcal F_A$. Since $d\nu_*=O(RdR\,da\,d\theta)$,

$$
\|t_L-f_*\|_2=O(q^2),\quad \|t_L\|_2^2=1+O(q^2).
\tag{25.15}
$$

Let $v_L=t_L/\|t_L\|_2$, positive for large $L$.

The frozen tail solves the zero-energy differential equation exactly:
for $R^{-1}\phi_{q^2}P$ its expression is
$R^{-3}\{-c\phi_{q^2}P''+(S-\gamma)\phi_{q^2}P\}$, which is zero
when $P''=-q^2P$. In the transformed numerator (25.7), its quadratic
part is a boundary term. Put
$\mathsf K_z=a_*^2m_0(\pi/2)\int c\phi_z^2da=\mathsf K+O(q^2)$.
The lower boundary of
$\mathsf K_z\int(P_L'^2-q^2P_L^2)dy=\mathsf K_z[P_LP_L']$
is canceled by the core flux (25.13) times $a_*^2m_0c_L^2$.
Core detuning costs $O(L^{-2}q^2(1+T)^3)$.
The actual kinetic errors cost $O(q^4)$, by integrating the derivative
bounds against $R^\gamma$. Signed actual-minus-frozen attraction and the
unchanged exterior contribute $R_b+O(q^2)$ plus an exponentially small
tail; multiplication by $-\lambda_Z/L^2$ gives
$-\lambda_ZR_b/L^2+o(L^{-3})$.

For explicit control, the inner splice, flux and coefficient errors
are bounded by

$$
C_5\{q^4(1+T)^8+q^2(1+T)^8e^{-\sigma T}
                         +r_L^\gamma q^2(1+T)^8\},
\tag{25.16}
$$

besides fixed-annulus $O(q^4)$ terms. The fixed-width product rule,
(25.14) and the $O(T^3)$ core attraction give this bound whenever
$q(1+T)\le1/10$. For the chosen $T$ it is $o(L^{-3})$.
Normalization changes this $O(L^{-2})$ numerator only by $O(L^{-4})$.
Thus the Rayleigh value $r(v_L)$ satisfies

$$
r(v_L)-E_*=\mathsf K_zq\cot\theta_L-\lambda_ZR_b/L^2+o(L^{-3}).
\tag{25.17}
$$

Expansion (25.12) gives
$q\cot\theta_L=-\nu^2\kappa_{\rm cap}/L^2
-Q_{\rm ang}\nu^4/(2CL^3)+O(L^{-4})$.
Since $\mathsf K\nu^2=\lambda_Z\mathsf D$, the trial expression is
exactly the right side of (25.2). A trial expression alone does not
identify the actual energy; the following residual closes that direction.

For an arbitrary angular test $f=f_*v\in\mathcal F_A$ put
$\|f\|_{\mathcal N}^2=B_\epsilon[v]+\|f\|_2^2$.
The core trace estimate and (17.10) give

$$
\begin{aligned}
\int_{T-1}^{T+2}\int\phi^2|v|^2&\le C_6(1+T)\|f\|_{\mathcal N}^2,\\
\int_0^{T+2}\int\phi^2|v|^2&\le C_6(1+T)^2\|f\|_{\mathcal N}^2.
\end{aligned}
\tag{25.18}
$$

These follow by integrating the mean derivative from its controlled core
trace, retaining the full angular remainder on enlarged annuli.
The deep-core capped multiplier is also controlled by $B_\epsilon[v]$.
The frozen tail residual is zero. Core detuning costs at most
$Cq^3(1+T)^4\|f\|_{\mathcal N}$; splice commutators are bounded by
(25.14) times a fixed additional polynomial in $1+T$ using (25.18).
Weighted Cauchy–Schwarz bounds the actual kinetic error by
$Cq^2\|f\|_{\mathcal N}$: on the tail,
$\int R^{2\gamma}h^2|\nabla_Hu_L|^2dq=O(q^4)$ and the core errors
are exponentially small. Equation (25.8) bounds the signed attraction
error by the same order. On $R<\epsilon/2$,
$|D_\epsilon-D_{0,\epsilon}|\le CR^{-1}\le C\epsilon R^{-2}$ is
absorbed by the core defect; on the cap collar use (25.18).
Here $D_{0,\epsilon}=\lambda_0(R^{-2}-\epsilon^{-2})_+$.
Relative core coefficient errors are $O(r_L^\gamma)$ and the fixed
outer cutoff costs $O(q^2)$. The ordinary mass pairing from
$r(v_L)-E_*=O(q^2)$ has that same order. Consequently

$$
\begin{aligned}
\mathcal R_L(f)&=q_{\epsilon,\lambda_Z}(v_L,f)
                                      -r(v_L)\langle v_L,f\rangle,\\
\|\mathcal R_L\|_{\mathcal N'}
 &\le C_7\{q^2+q^3(1+T)^8+q(1+T)^8e^{-\sigma T}
                          +r_L^{\gamma/2}q(1+T)^8\}=O(L^{-2}).
\end{aligned}
\tag{25.19}
$$

The norm equivalence following (25.10) makes this also the bound in
$a_\epsilon'$ uniformly in $L$. These are form and first-derivative
estimates for all tests, not a singular pointwise $L^2$ residual.

Let $e_j$ be the actual eigenvalues and $v_j$ the coefficients of $v_L$
in their orthonormal eigenbasis. The spectral theorem gives

$$
\|\mathcal R_L\|_{a_\epsilon'}^2
             =\sum_j\frac{|e_j-r(v_L)|^2|v_j|^2}{e_j+\beta}.
\tag{25.20}
$$

The uniform first gap and $r(v_L)\to E_*$ imply, for $j\ge2$,
$e_j-e_1\le C_8(e_j-r(v_L))^2/(e_j+\beta)$, also at arbitrarily large
$e_j$. Thus
$0\le r(v_L)-e_1\le C_8\|\mathcal R_L\|_{a_\epsilon'}^2=O(L^{-4})$.
The analogous inequality with $e_j+\beta$ controls the higher spectral
component in $a_\epsilon$ norm by $O(L^{-2})$. Positivity fixes the
first coefficient's sign and its normalization correction is $O(L^{-4})$.
This proves (25.2)–(25.3) for the actual unrestricted minimum, including
the negative third term if the second cancels.

For resources, $\langle\phi_z,\phi\rangle=M$ implies
$\int\phi_z^2=M+O(q^4)$. Direct sine integration gives
$\int_0^LP_L(y)^2dy=L/2+\kappa_{\rm cap}+O(L^{-1})$.
Replacing the elementary profile below $T$ by its exact core changes
attraction by $O(q^2(1+T)^3)=o(1)$.
The signed density and unchanged exterior give $R_b+o(1)$;
normalization costs $O(Lq^2)=o(1)$. Hence
$\mathcal W_\epsilon[v_L/f_*]=\mathsf D L/2+S_b+o(1)$.
For $h_L=f_{\epsilon,\lambda_Z}-v_L$, (25.3) gives
$B_\epsilon[h_L/f_*]+\|h_L\|^2=O(L^{-4})$, and (25.10) gives
$\mathcal W_\epsilon[h_L/f_*]=O(L^{-2})$.
Positive-multiplier Cauchy–Schwarz transfers the finite part with error
$O(L^{-1/2})=o(1)$.

Direct core dilation of $v_L$ gives
$L^2\int D_\epsilon|v_L|^2d\mu\to
 a_*^2m_0\lambda_0\nu^2 I$.
The defect is a summand of $B_\epsilon$; the actual-state cross error
is $O(L^{-3})$ before multiplication by $L^2$. Dividing by
$g_{\mathrm c}$ proves the last line of (25.4). The difference is
$o(1)$, so raw and capped finite parts agree. The exact finite-domain
identity $T_A=E_{\epsilon,\lambda_Z}+
 g_{\mathrm c}(1+\lambda_Z/L^2)V_{\rm cap}$ gives the kinetic finite
part. No differentiation of (25.2) is used. Finally the reference rule
in (25.1) gives $S_b=\mathsf D\log(b_{\rm bal}/b)$ and all asserted
cancellation alternatives. $B_3>0$ excludes any further cancellation at
this order. $\square$

## 26. Source correspondence, attribution and the remaining response problem

The constants above retain every normalization in (10.2), (10.6),
(10.9) and Definition 14.1. In particular the inverse native Jacobian
is $1/(2r)$, the graded covariance change contributes $\det A(o)$,
the angular period is $2\pi$, the polar Jacobian is $1/4$, and
$m_0c_G=1/(2\pi)$. The full killed unit-source Green field is used at
all times; the cap changes a multiplier, not the source or the domain.
Auxiliary gauge balls and annuli are matching surfaces, not new killed
walls or holes. The frozen rotational solutions are comparison and
limit objects; no rotational restriction is imposed on the actual
smooth density, SPD matrix or normalized states.

Under $\rho\mapsto c_1\rho$, $c_1>0$, the covariance rule of §19 gives
$m_0\mapsto c_1m_0$, $a_*\mapsto c_1^{-1/2}a_*$,
$\Gamma\mapsto\Gamma/c_1$, $g_{\mathrm c}\mapsto c_1g_{\mathrm c}$.
The operators, energies, kinetic costs and
$\mathsf K,\mathsf D,R_b,B_3,b_{\rm bal}$ are invariant.
Raw and capped attraction costs acquire the inverse density factor.
The source Green-pairing coefficient $K$ itself scales by $c_1$, as
its vectors were normalized by $h$ rather than by global $L^2$ mass.
All scales refer to the original clock with covariance $2A\,dt$.
There is no uniformity claim over different $\rho,A$, moving sources,
changing chart radii or spectral resonances. The compact-parameter
uniformities in §§22–24 and the auxiliary subthreshold gap in §25 have
their explicitly narrower scopes.

The sharp original-domain classification in §§10–13 and the exactly
critical selection, trace and cap/resource laws in §§14–19 are reused.
The different temporal family in
[Critical cutoff, Definition 31.1](FIB_NATIVE_CRITICAL_CUTOFF_SPECTRAL_LIMITS.md)
varies moving-time multipliers and a carrier parameter. The interaction
in [Weak binding, Definition 70.1 and Proposition
70.2](FIB_NATIVE_LONG_TIME_PHASE_WEAK_BINDING.md) is on the real cover,
with changed threshold source $SW_\tau=F(\tau;\cdot)$ and different
behaviour at infinity. [Continuation III, Specification 82.7 and Theorem
87.4](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md)
gives an elementary bounded-cap bound and a different added-kinetic-law
completion. These are useful neighbouring results, with different
source/operator/domain contracts. The finite normalized-law, binary-task,
zero-one-loss setting of
[Task information and Bayes risk](FIB_ATOM_TASK_INFORMATION_BAYES_RISK_GEOMETRY.md)
supplies no Green or resource theorem for (20.1); its information and risk
quantities are distinct.

For primary attribution, Derkach–Hassi–Malamud–de Snoo,
[§4.1 and Proposition 4.2](https://arxiv.org/html/math/0610299v1),
supplies the abstract ordinary boundary-triplet and intermediate-extension
resolvent machinery. Theorem 21.1 proves its native hypotheses:
closed symmetry, equal defects, graph-bounded maps, full range and Green
identity. Its convention here is $\Gamma_0=\mathcal B$,
$\Gamma_1=-K\mathcal A$, reference operator $F$, and boundary relation
$\Theta=-K\kappa$. The resolvent formula applies at a reference
resolvent point where $\Theta-M(z)$ is invertible. Their Theorem 7.2
has its stated Weyl/gamma-field and generalized-resolvent conditions;
it does not compute this model's Weyl function or select the cap limit.

Dereziński–Richard,
[§§2.2–2.3 and Theorem 5.5](https://arxiv.org/html/1604.03340v2), treats
scalar half-line inverse-square operators with specified boundary
families. Camblong–Epele–Fanchiotti–García Canal,
[equation (1)](https://arxiv.org/html/hep-th/0003014v2),
Braaten–Phillips, [equation (4)](https://arxiv.org/html/hep-th/0403168v1),
and Bouaziz–Bawin, [the medium-to-weak radial
setting](https://arxiv.org/html/1402.5325v1), concern Euclidean radial
reductions and their cutoff/extension prescriptions. Their Bessel
constants and endpoint parameters are not imported into the finite-energy
angular equation (22.17). D'Arca–Fanelli–Franceschi–Prandi,
[Theorem 1.2](https://arxiv.org/html/2603.04086v1), provides the
unweighted Hardy lower bounds already attributed in §10, rather than
the exact cap phase or its global response.

Vázquez–Zographopoulos,
[the critical weighted-completion setting](https://arxiv.org/html/1102.5661),
and Felli–Ferrero,
[Theorem 2.1 and Corollaries 2.2–2.3](https://arxiv.org/html/1209.4852v1),
provide Euclidean critical-Hardy and cylindrical context.
Abatangelo–Felli–Hillairet–Léna,
[Theorems 1.4, 1.7 and Appendix A](https://arxiv.org/html/1611.06750v1),
and Abatangelo–Bonnaillie-Noël–Léna–Musolino,
[Theorems 1.1 and 6.2](https://arxiv.org/html/1911.06686), study
Euclidean Dirichlet holes and eigenfunction capacity; the latter
Theorem 6.2 includes its positive vanishing-order hypothesis.
Their spectral approximation motivates comparison, but neither its
domain nor its capacity coefficients replace the form residual and gap
argument (25.18)–(25.20). The native deductions here are supported by
the displayed source identities, variational arguments and ordinary
proofs, with no exhaustive literature or priority assertion.

The remaining mathematical interface is the actual cap-to-global
finite-energy response on the original killed cylinder. The local domain
classification lists possible source realizations; it does not choose
one. The frozen phase describes an auxiliary zero-energy response;
Theorem 22.3 estimates an interior map relative to arbitrary actual trace.
Neither selects the full finite-energy trace returned by the outer
cylinder. Proposition 22.4 explains why scalar separation cannot supply
that missing map. At $\lambda_D$, boundedness from Proposition 24.2 is
not convergence: the limiting energy, selected realization, normalized
state and separate resources, including any additional necessary scale
or global data, remain to be determined.

A complete all-real-$\lambda$ finite-parameter operator classification
must also control all exceptional or resonant values and the remaining
spectral subspace above the first threshold. In the triplet of §21,
for $z\in\rho(F)$ the native Weyl solution has a global ratio
$m_{\mathcal A}(z)=\mathcal A/\mathcal B$.
For a specified line $\mathcal A=\kappa\mathcal B$, its rank-one
resolvent denominator is proportional to $m_{\mathcal A}(z)-\kappa$;
real poles of the reference realization require their own spectral
bookkeeping. The uncomputed cap-selected ratio and the global Weyl
response cannot be replaced by $\kappa_{\rm cap}$ or by the frozen
nodal radius. The positive ground-profile theorem and the sharp collapse
laws in §24 do not establish convergence of the whole resolvent.
Sharp actual state and separate-resource laws outside the regimes proved
here, with their necessary compact-parameter uniformity, remain part of
that same unchanged problem. The exactly critical case remains supplied
by §§14–19. The current-ray dimension, direct rank, growth and homogeneous
volume exponent keep their distinct meanings from §2; none of these
analytical results identifies a physical Euclidean dimension.

## 追加锚（本行以下为增补区）

## 27. Source parameters for the retained and resonant ground limits

With the fixed $b$ of (20.1), use the source coordinate
$x=\log(R/b)$. The corresponding constant trace is
$\mathcal A_b=\mathcal A+\mathcal B\log b$. Thus, for
$\eta_b=\log b-\kappa_{\rm cap}$,

$$
\mathcal A+\eta_b\mathcal B
                =\mathcal A_b-\kappa_{\rm cap}\mathcal B.
\tag{27.1}
$$

The actual inherited-wall response and the positive-ground limits for
$\lambda<\lambda_D$, equality, and the
$\lambda_D+\sigma/L$ precision window are developed in
[Native spatial-cap retained and resonant ground-state limits,
§§1–10](FIB_NATIVE_SPATIAL_CAP_RETAINED_AND_RESONANT_LIMITS.md).
Its constants are exactly (20.2), with $K=m_0k$ and
$\mathsf K=a_*^2K$; its equality normalization is the global response
amplitude $a_D$. It supplies the retained/equality ground conclusions
in the source correspondence of §26. Rank-one ground projections
and the associated resource laws are distinct from the full operator
classification on all spectral subspaces.

## 追加锚（本行以下为增补区）

## 28. Scope reconciliation with the complete combined theory

The two closing paragraphs of §26, beginning “The remaining
mathematical interface” and “A complete all-real-$\lambda$”, describe
what the preceding §§20–26 alone leave unresolved. Their descriptions
of the retained/equality ground limits and the all-real nonreal-resolvent
classification as unresolved are superseded and void for the complete
combined theory. The local limitations of the domain classification,
frozen phase and interior trace estimate remain as stated; they are
not independent suppliers of the companion's conclusions.

The ground replacement is the companion source,
[Native spatial-cap retained and resonant ground-state limits,
§§1–10](FIB_NATIVE_SPATIAL_CAP_RETAINED_AND_RESONANT_LIMITS.md),
with the source correspondence (27.1). Its Theorem 2.2 supplies
retention below $\lambda_D$; Theorem 6.1 supplies the inherited-wall
response used by Theorems 7.1–9.1 for the equality ground, sharp energy,
profile and separate resources. Corollary 10.1 supplies the stated
first-threshold precision window. This owner's Theorem 24.1 supplies
superthreshold collapse, Theorem 25.2 the $\lambda_Z$ cancellation,
and §§14–19 the exactly critical laws, each at its original scope.

The operator replacement is the companion's Theorem 12.1, with proof
in §§13–19 and ground compatibility in §20. For the unchanged family
(20.1), its (12.4)–(12.5) classify every fixed real $\lambda$,
including all $\lambda_n$, for each fixed model, admissible $b$, fixed
$L^2(\mu)$ input and nonreal $z$. Its (12.6)–(12.7) give the resonant
third-order window. Compact uniformity is exactly that theorem's:
away from resonances in $\lambda$, or on compact window-parameter
sets with uniform remainder, for each fixed input and compact nonreal
$z$ set. The original capped domain and the
selected limiting source domains are distinguished in its §12.

These suppliers preserve every preceding theorem's hypotheses and
conclusions. Strong-resolvent convergence does not supply normalized
ground or resource convergence. No general cap-to-fixed-radius
operator-norm response estimate or global real-pole analysis is claimed
by the graph-core route; neither is needed for its nonreal resolvents
(companion, §20). Norm-resolvent convergence, quantitative rates,
all-level counts, arbitrary varying-$\lambda$ sequences,
model-uniformity and new resource finite parts remain outside its
conclusions (companion, Theorem 12.1 and §§20–21). The dimension and
acquisition distinctions of §26 remain in force.

## 追加锚（本行以下为增补区）

## 29. Finite native command laws generating the complete free Green occupation

Write N for [Probability, phase transport and holonomy](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md)
and K for [Guarded lift limits](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md).
The construction below uses N's original commands and K's path contracts.
Its sampling and coefficient capabilities are additional premises. Neither
convergence nor a lifetime-tail estimate is a premise.

**Definition 29.1 (fixed model and additional sampling capability).** Fix any
both-wall model of §§1–3, any smooth positive raw density $\rho$, any smooth
horizontal SPD matrix $A$, and any interior source $o=(k_o,\alpha_o,\beta_o)$.
Thus $H=r/2$, $I=(l,u)\Subset(0,H)$, $X_1=P$, $X_2=Q$ are (2.1),
$\Omega=I\times\mathbb T^2$, and $d\mu=\rho\,dk\,d\alpha\,d\beta$.
Both phases retain period $2\pi$ and their fixed preparation rotations.
Put $\Sigma=A^{1/2}$ and define the two real functions

$$
d^j(q)=\rho(q)^{-1}\sum_{i=1}^2 X_i(\rho a^{ij})(q),\qquad j=1,2.
\tag{29.1}
$$

The added capability supplies, for each finite stage, finitely many
independent fair signs, the specified initial state and means, exact real
arithmetic and evaluations of $\Sigma,d$ at recursively computed states,
and execution of the prescribed original piecewise linear controls in their
specified durations. Evaluation of $d$ includes the coefficient derivatives
in (29.1). Exact calculation of a chord's first wall-hit fraction is included.
These are mathematical/operational premises, with no asserted price,
precision guarantee, sensor, preparation procedure or archive implementation.
A whole finite command can be computed before execution; unknown-state
feedback is not supplied or required by that calculation.

For real controls and chronological area write the original map as

$$
\Phi_o(a,b,j)=\left(k_o+a,\ [\alpha_o+b/2],\
 [\beta_o+c_o b-j/r]\right),\qquad c_o=\tfrac12-k_o/r.
\tag{29.2}
$$

This is N, Theorem 9.3, in the actual unimodular torus coordinates (2.1),
at every prefix. In particular $j=\int a\,db$ for a finite command.
The source real relation lift is translated by $b$; it is not reset at joins.

**Definition 29.2 (an explicit finite law).** For integers $n\ge1$ set
$\delta_n=n^{-2}$, $m_n=n^3$, $S_n=m_n\delta_n=n$ and
$T_n=S_n+\delta_n$. Draw $m_n$ independent vectors
$\xi_i=(\xi_i^1,\xi_i^2)$, each uniform on $\{-1,1\}^2$.
Starting with $(a_0,b_0,j_0)=(0,0,0)$, at an alive node $t_i=i\delta_n$
compute $q_i=\Phi_o(a_i,b_i,j_i)$ and the two-control increment

$$
v_i=d(q_i)\delta_n+\sqrt{2\delta_n}\,\Sigma(q_i)\xi_i.
\tag{29.3}
$$

During this cell use the constant control velocity $v_i/\delta_n$.
Writing $\theta=(t-t_i)/\delta_n$, its comparison prefix is exactly

$$
\begin{aligned}
a(t)&=a_i+\theta v_i^1,& b(t)&=b_i+\theta v_i^2,\\
j(t)&=j_i+\theta a_i v_i^2+\tfrac12\theta^2v_i^1v_i^2.
\end{aligned}
\tag{29.4}
$$

If its height first reaches $l$ or $u$, cut this chord at that first hit and
hold both controls for the rest of $[0,T_n]$. Otherwise use (29.4) at
$\theta=1$ as the next node, without resetting $j$. If all $m_n$ cells
survive, use the last interval $[S_n,T_n]$ to move height linearly from its
current value to $u$, with $b$ constant, then hold. Denote the resulting
command by $(\widehat a_n,\widehat b_n)$, its actual ordinary integral by
$\widehat j_n=\int\widehat a_n\,d\widehat b_n$, its held state by
$\bar q_n=\Phi_o(\widehat a_n,\widehat b_n,\widehat j_n)$, and its first
wall-hit time by $\zeta_n$. Constant continuation beyond $T_n$ represents
paths without adding executed command duration.
The killed observation is $q_n^\dagger(t)=\bar q_n(t)$ for $t<\zeta_n$
and $\dagger$ for $t\ge\zeta_n$. Unused signs are simply unused; no draw
is rejected or reweighted by survival.

**Lemma 29.3 (literal lawfulness and finite resources).** Every realization
of Definition 29.2 is an original absolutely continuous, piecewise linear,
zero-start command on a finite interval. Its lifetime satisfies
$0<\zeta_n\le T_n$, and every prefix obeys

$$
k_o+\min\widehat a_n\ge l>0,\qquad
k_o+\max\widehat a_n\le u<H.
\tag{29.5}
$$

Its state and area are (29.2) and the same ordinary integral, including the
possibly partial final chord. Both actual height walls are used for killing.

Proof. The height on a chord is affine, so its exact first hit is computable
from its initial height and $v_i^1$. If both endpoints lie inside $I$, the
whole chord does; if it leaves, the executed portion ends at its first face.
Thus checking endpoints to compute that fraction misses no within-cell
exit. The extra terminal leg lies inside $[l,u]$ and reaches $u$.
There are finitely many chords and at most one partial chord. Their holds
and joins are absolutely continuous. Integrating $a\,db$ on a partial
chord gives (29.4); the terminal height leg has $db=0$. N, Theorems 9.2–9.3,
therefore give (29.5) and (29.2) for the complete original history.
A killing face is inside the original native source $(0,H)$, so holding
there is lawful even though its killed observation is already dead.

On $\overline\Omega$, boundedness gives $|v_i|\le C\sqrt{\delta_n}$.
Consequently the executed total control variation is at most
$C m_n\sqrt{\delta_n}+(u-l)$. If the additional norm of N, §10.1,
is used, its length is bounded by a fixed multiple of that quantity and
its quadratic energy by $C(m_n+(u-l)^2/\delta_n)$. These follow by
integrating the actual velocities for their actual elapsed fractions;
$A^{-1}$ is uniformly bounded on the closed cylinder. All are finite at
each stage. These bounds are not uniform as the mesh vanishes and do not
price sampling or coefficient access. A command precomputed for $o$ is
one numerical command; at another start its lawful domain is still N's
extrema domain, not a recomputed cutoff. $\square$

**Lemma 29.4 (joint enhanced approximation, with the density drift).**
Before exit, the comparison triples of (29.3)–(29.4) converge in law,
uniformly on every fixed compact time interval, to $Z=(U^1,U^2,J)$ with

$$
\begin{aligned}
dU^i_t&=d^i(Q_t)\,dt+\sqrt2\sum_a\Sigma_{ia}(Q_t)\,dB^a_t,\\
J_t&=\int_0^t U_s^1\,dU_s^2+\int_0^t a^{12}(Q_s)\,ds
    =\int_0^t U_s^1\circ dU_s^2,\qquad Q_t=\Phi_o(Z_t).
\end{aligned}
\tag{29.6}
$$

Here $B$ is standard two-dimensional Brownian motion, the first integrals
are Itô integrals, and the assertion before exit is obtained by localization
from the comparison extensions in the proof. In the original clock,

$$
\mathcal G f=\sum_jd^jX_jf+\sum_{i,j}a^{ij}X_iX_jf
=\rho^{-1}\sum_{i,j}X_i(\rho a^{ij}X_jf)=-L_Af.
\tag{29.7}
$$

In particular $d[U^i,U^j]_t=2a^{ij}(Q_t)dt$, with the full cross term.

Proof. Choose a slightly larger height interval with compact closure in
$(0,H)$ and inside the given coefficient neighbourhood. Extend $\Sigma,d$
smoothly, periodically in phases, to all real
heights, with bounded derivatives and bounded values. This can be done by
interpolating $A$ to a constant SPD matrix outside a larger collar and
then taking its square root, and extending $d$ separately by a cutoff.
The extensions equal the original functions on a neighbourhood of $[l,u]$;
their relation to $\rho$ outside that neighbourhood is immaterial.
Continue the recursion with fresh independent signs for comparison only.
Its part up to the first wall hit is exactly the executed recursion.
No post-exit comparison path is asserted to be an original lawful history.

On the real triple space put $D_1=\partial_a$ and
$D_2=\partial_b+a\partial_j$. A chord is the time-one flow of
$v^1D_1+v^2D_2$, hence has precisely (29.4). At a node, conditionally on
the past $\mathcal F_i$, its moments are

$$
\mathbb E_i v^j=d^j\delta,\qquad
\mathbb E_i(v^iv^j)=2a^{ij}\delta+d^id^j\delta^2,\qquad
|v|\le C\sqrt\delta\quad(\delta\le1).
\tag{29.8}
$$

All coefficients here are evaluated at $\Phi_o(Z_i)$ and are frozen during
the chord. Taylor expansion along that flow gives, locally uniformly for
smooth tests $F$, the one-step generator

$$
\delta^{-1}\mathbb E_i\{F(Z_{i+1})-F(Z_i)\}
=\mathscr A F(Z_i)+O_K(\sqrt\delta),\qquad
\mathscr A=\sum_jd^jD_j+\sum_{i,j}a^{ij}D_iD_j.
\tag{29.9}
$$

Here $K$ is any fixed compact subset of triple space. The third-order
remainder is $O_K(|v|^3)$; the $\delta^2d^id^j$ term in (29.8) is
also harmless after division by $\delta$. For $F\in C_c^\infty$, the
error is globally $O_F(\sqrt\delta)$: each $D_{i_1}\cdots D_{i_s}F$,
$s\le3$, is bounded, since its polynomial factors in $a$ multiply
compactly supported derivatives. This verifies the generator rather than
assuming an enhanced invariance principle.

For completeness, the following bounds justify compactness and passage to
the martingale problem. Decompose $a_i,b_i$ into their conditional drifts
and martingale differences. Their drifts are bounded by $C\delta$ and
their conditional martingale variances by $C\delta$. Doob's inequality
therefore bounds their expected squared maxima on $[0,R]$ by $C_R$.
The exact third increment is $a_i v_i^2+v_i^1v_i^2/2$. Its conditional
mean is

$$
a_i d^2\delta+a^{12}\delta+\tfrac12d^1d^2\delta^2,
\tag{29.10}
$$

and its centered conditional second moment is at most
$C(1+a_i^2)\delta$. Cauchy–Schwarz for the drift sums, followed by
Doob for the martingale sums, now gives
$\mathbb E\max_{i\delta\le R}|Z_i|^2\le C_R$. Include one extra cell
when $R$ is not a node. Chord maxima have the same bound by (29.4).
This proves compact containment, uniformly as $\delta\downarrow0$.

Stop the node chain on leaving a ball of radius $K$. Each coordinate's
martingale jumps are at most $C_K\sqrt\delta$, its optional quadratic
variation increases by at most $C_K\delta$ per step, and its drift
increases by at most $C_K\delta$ per step. Thus the brackets have modulus
at most $C_K(|t-s|+\delta)$, and the martingales are C-tight by the
bounded-jump bracket criterion of Whitt, Theorem 3.7, cited below.
The drifts are C-tight by the same deterministic modulus bound.
The stopped and original paths differ before $R$ with probability at most
$C_R/K^2$, by compact containment. Letting $K\to\infty$ removes this
localization. The piecewise constant
node processes consequently have continuous subsequential limits. Their
largest jumps tend to zero in probability, so linear interpolation has
the same limits in the uniform topology. Its third
coordinate differs from the chord integral by
$\tfrac12(\theta^2-\theta)v_i^1v_i^2$, at most $C\delta$; the other
coordinates agree. The actual continuous comparison triples are therefore
tight in the uniform topology with these same limits.

For $F\in C_c^\infty$, subtract its exact conditional one-step means
from the piecewise constant node test process to obtain a martingale.
The global version of (29.9) replaces its compensator by the Riemann sum
of $\mathscr A F$ with error $O_{F,R}(\sqrt\delta)$. Both $F$ and
$\mathscr A F$ are globally bounded, so these test martingales are bounded
uniformly on $[0,R]$. Joint convergence of the node paths and their
compensators follows from continuity of the limiting path and the Riemann
sums. Martingale preservation under uniform integrability, as in Whitt,
Theorem 5.3, therefore passes the martingale identity to each limit.
Equivalently one passes its expectation against bounded continuous tests
of finitely many past coordinates and then uses a monotone class.
This step needs no ball-hitting-time continuity. Every limit solves the
martingale problem for $\mathscr A$.

That martingale problem is unique. In coordinates its drift is
$(d^1,d^2,a d^2+a^{12})$ and its noise columns are
$\sqrt2(\Sigma_{1s},\Sigma_{2s},a\Sigma_{2s})^{\mathsf T}$.
They are locally Lipschitz and have linear growth, so the SDE has a unique
nonexplosive strong solution. To check equivalence with the martingale
problem even though its three-dimensional symbol has rank two, apply the
problem to coordinate and quadratic-coordinate tests with compact cutoffs.
The first two martingale coordinates have bracket $2A\,dt$; multiplication
by $(\sqrt2\Sigma)^{-1}$ gives a Brownian motion by Lévy's characterization.
The third martingale minus $\int a\,dM^2$ has zero bracket and is zero.
This gives exactly (29.6), proving uniqueness of the whole joint limit.
All subsequences therefore have that limit.

Finally $d\Phi_o(D_i)=X_i$, so pushing (29.9) forward gives (29.7).
Both $X_i$ have zero divergence for $dk\,d\alpha\,d\beta$; (29.1)
therefore gives exactly the operator represented by form (1.1).
Equivalently, if $Y_s=\sum_i\Sigma_{is}X_i$ and
$\kappa_s=\rho^{-1}\sum_iX_i(\rho\Sigma_{is})$, then
$d^j=\sum_s\kappa_s\Sigma_{js}+\sum_sY_s\Sigma_{js}$.
Thus the Stratonovich state equation has noise $\sqrt2Y_s$ and drift
$\sum_s\kappa_sY_s$, precisely the original divergence-form law.
In actual lifted state coordinates the Itô drift is
$(d^1,d^2/2,c(k)d^2-a^{12}/r)$; the term $-a^{12}/r$ comes from the
same chord area. There is no third driver, missing density drift, extra
area drift or clock renormalization. $\square$

**Lemma 29.5 (mesh-uniform full-lifetime tail).** There are constants
$h,M<\infty$ and $n_0$, depending only on this fixed model and interval,
such that the commands above satisfy, for $n\ge n_0$, $t\ge0$ and $R\ge1$,

$$
\mathbb P(\zeta_n>t)\le
2^{-\lfloor (t-1)_+/h\rfloor},\qquad
\mathbb E(\zeta_n-R)_+\le
2h\,2^{-\lfloor(R-1)/h\rfloor}.
\tag{29.11}
$$

Proof. Let $a_* =\min_{\overline\Omega}a^{11}>0$ and
$D=\max_{\overline\Omega}|d^1|$. Choose $\lambda>0$ with
$\lambda^2a_* -\lambda D>2$. While the height $K_i$ is inside $I$,
independent fair signs give the exact conditional expression

$$
\mathbb E_i e^{\lambda v_i^1}
=e^{\lambda d^1\delta}\prod_{s=1}^2
 \cosh(\lambda\sqrt{2\delta}\Sigma_{1s}),\qquad
\log\mathbb E_i e^{\lambda v_i^1}
=\delta(\lambda d^1+\lambda^2a^{11})+O(\delta^2).
\tag{29.12}
$$

The error is uniform on the closed cylinder. For all sufficiently small
$\delta$ the right side is at least $\delta$, hence
$\mathbb E_i(e^{\lambda K_{i+1}}-e^{\lambda K_i})\ge e^{\lambda l}\delta$.
Use the infinitely continued comparison chain only until its first node
$N\ge1$ outside $I$. Bounded increments imply that its stopped height
always lies in $[l-C,u+C]$ for $\delta\le1$, including its last overshoot.
For each deterministic integer $m$, summing conditional expectations gives

$$
e^{\lambda l}\delta\,\mathbb E(N\wedge m)
\le\mathbb E e^{\lambda K_{N\wedge m}}-e^{\lambda K_0}
\le e^{\lambda(u+C)}.
\tag{29.13}
$$

Thus $\mathbb E(N\delta)\le M:=e^{\lambda(u+C-l)}$, uniformly over
every initial alive height and both phases. This proves $N<\infty$
almost surely without assuming optional stopping at an unbounded time.
With $b_\delta=\lceil2M/\delta\rceil$, conditional Markov inequality
and the fresh signs give survival at most $1/2$ over each group of
$b_\delta$ steps, from every surviving node. Induction yields
$\mathbb P(N>j b_\delta)\le2^{-j}$. Since
$b_\delta\delta\le h:=2M+1$, the polygon's exact first-hit time
$\tau_\delta\le N\delta$ satisfies
$\mathbb P(\tau_\delta>t)\le2^{-\lfloor t/h\rfloor}$.
The argument uses the whole state in its conditioning and permits all
phase dependence, height drift and cross terms.

Couple the finite command with this chain using its first $m_n$ signs.
If it dies by $S_n$, $\zeta_n=\tau_{\delta_n}$. Otherwise its terminal
leg gives $\zeta_n=S_n+\delta_n\le\tau_{\delta_n}+\delta_n$.
Therefore $\mathbb P(\zeta_n>t)$ is bounded by the survival estimate
shifted by at most $\delta_n\le1$. Integrating that geometric step
bound on $[R,\infty)$ proves (29.11). This is a proved lifetime-tail
bound for the constructed laws, not an additional calibration condition.
$\square$

**Theorem 29.6 (existence of a full source-faithful command/Green bridge).**
Under precisely the additional capabilities in Definition 29.1, for every
admitted fixed $\rho,A$ and every original interior preparation $o$, the
laws of Definition 29.2 have the following joint limits. Let $Q$ be the
free diffusion (29.6)–(29.7), $\tau$ its first height exit from $I$, and
$Z^\tau=(U^1,U^2,J)_{\cdot\wedge\tau}$ its held enhanced history.
For each $R>0$, the held triples converge on $[0,R]$ in
$C([0,R],\mathbb R^3)$ with the uniform topology, jointly with the held
state paths in $C([0,R],\overline\Omega)$, the censored lifetimes, and

$$
q_n^\dagger\ \Longrightarrow\ Q^\dagger
\quad\hbox{in }D([0,R],E)\hbox{ with }J_1,\qquad
E=\overline\Omega\sqcup\{\dagger\}.
\tag{29.14}
$$

Use K, Definition 4.1's truncated product metric on $\overline\Omega$,
with the cemetery isolated at distance $2$. A lifetime exceeding $R$ is
represented by the isolated no-death mark $\infty$, as in K, Theorem 4.2.
The real full lifetimes also satisfy $\zeta_n\Rightarrow\tau<\infty$,
jointly with these paths. For every continuous real or complex $f$ on the
closed cylinder,

$$
\lim_{n\to\infty}\mathbb E\int_0^{\zeta_n}f(\bar q_n(t))\,dt
=\mathbb E_o\int_0^\tau f(Q_t)\,dt
=\int_\Omega\Gamma_{A,o}(q)f(q)\,d\mu(q).
\tag{29.15}
$$

Here $\Gamma_{A,o}$ is the original complete free Dirichlet Green field
for its raw-$\mu$ unit source, including all times. These assertions retain
both actual killing faces, all-prefix native guards, original preparation
phases and torus periods, and the common chronological area and trajectory.
No phase independence or restriction on the size of coefficient variation
is imposed; constants may depend on the fixed model.

Proof. Lemma 29.4 supplies comparison-triple convergence on each fixed
horizon. The limit has height drift $d^1$ bounded near the closed cylinder
and height bracket $2a^{11}dt$ bounded above and below by positive constants.
It exits in finite time: applying Itô's formula to $e^{\lambda K}$ at
$t\wedge\tau$, with the $\lambda$ of Lemma 29.5, bounds
$\mathbb E(t\wedge\tau)$ uniformly, since
$\mathcal G e^{\lambda k}=e^{\lambda k}(\lambda d^1+\lambda^2a^{11})$
is bounded below by a positive constant on $\overline\Omega$.
Monotone convergence gives $\mathbb E\tau<\infty$.

At either exit the height strictly crosses outside $[l,u]$ in every
subsequent time interval almost surely. Indeed, after that stopping time
its continuous martingale part has clock between positive multiples of
elapsed time, while its drift is $O(t)$. The Brownian oscillation law after
the continuous-martingale time change gives both signs with magnitude
larger than $O(t)$ arbitrarily close to zero. Localizing to the coefficient
collar suffices. This verifies exactly K's strict-crossing hypothesis.
There is no atom at a fixed $R>0$: choose a slightly larger interval $I'$
inside the original coefficient neighbourhood and $(0,H)$. Kill the smooth
comparison diffusion only at the ends of $I'$. N, Theorem 10.7, with the
all-start SDE identification recalled below, gives its smooth interior
heat density. The two faces of $I$ are interior measure-zero surfaces in
$I'\times\mathbb T^2$. On $\{\tau=R\}$ this larger-domain process is
still alive at $R$ and lies on one of those surfaces, an event of probability
zero. This uses the supplied bracket-generating fields $P,Q,[P,Q]$.
The initial interior margin also gives $\tau>0$ almost surely.

For $n>R$ the terminal leg starts after $R$, so it has no effect on any
path or death flag on $[0,R]$. K, Theorems 3.1 and 4.2, applied to
Lemma 29.4 and these crossing/no-atom facts, give all the asserted joint
held/censored/$J_1$ limits. The boundary point is the left limit at death;
the cemetery begins at death. Uniform convergence of killed paths is not
asserted. Full step-two increments are recovered continuously
from $J_t-J_s-U_s^1(U_t^2-U_s^2)$, the two squared increments and integration
by parts. Thus they converge jointly as well; no area is sampled separately.
The topology here is the inherited uniform chronological-triple topology,
not an unasserted rough-path variation topology. The geometric tail of
Lemma 29.5 and the censored lifetime convergence give the real lifetime
convergence jointly with the paths: truncate at a horizon beyond the path
horizon, then let that truncation tend to infinity using (29.11).
The limit inherits the integrable survival bound too.

The diffusion just identified is the original free killed Friedrichs law.
Indeed (29.7) has exactly form (1.1), and killing is at its two
noncharacteristic height faces with periodic phases. The absorbing
part-form identification, including its extension to every interior start,
is already supplied in [Free diffusion quotient rigidity, Theorem 3.1's
proof of (3.12)–(3.14)](FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md).
That identification uses no coefficient symmetry; symmetry is needed only
for that source's additional descent assertion. It is reused here with
$Y_s=\Sigma_{is}X_i$, drift $\sum_s\kappa_sY_s$, and zero potential.
Thus no exceptional preparation, different operator domain or ground
conditioning has been inserted.

Set $f^\dagger(\dagger)=0$. On $[0,R]$ the occupation functional
$\omega\mapsto\int_0^R f^\dagger(\omega(t))dt$ is bounded and is continuous
at each target path in (29.14). The $J_1$ time changes align the sole
cemetery jump, and away from that jump the continuous alive path and the
uniform continuity of $f$ give convergence in measure, hence of the
bounded integrals. Therefore the finite-horizon expected occupations
converge. The omitted complete occupation is bounded in absolute value by
$\|f\|_\infty\mathbb E(\zeta_n-R)_+$, which tends to zero uniformly
by (29.11). The target tail tends to zero as well. Taking first
$n\to\infty$ and then $R\to\infty$ proves the first equality in (29.15).

Finally the original heat density is relative to the same unnormalized
$d\mu$, and its row mass is $\mathbb P_o(\tau>t)$. The full Green
supplier in §1 gives $\Gamma_{A,o}(q)=\int_0^\infty p_t^\Omega(o,q)dt$.
Tonelli applied to positive and negative parts, and separately to real and
imaginary parts when needed, justified by
$\|f\|_\infty\mathbb E_o\tau<\infty$, proves the second equality.
Equivalently its weak source identity is
$\int\Gamma_{A,o}L_A\varphi\,d\mu=\varphi(o)$ for compactly supported
smooth $\varphi$, from Dynkin's formula and the vanishing terminal killed
term. There is no probability normalization of $\mu$, torus averaging,
extra factor $1/2$, or time truncation in this unit-source identity.
$\square$

**Boundary 29.7 (resources, suppliers and interpretation).** For each fixed
$R>0$, both limiting held controls on $[0,R]$ have infinite total variation almost
surely: $\tau>0$ and $a^{11},a^{22}>0$ give nonzero quadratic variation
before death. The sets of continuous paths with total variation at most
$B$ are closed in the uniform topology. The held convergence and the
Portmanteau inequality therefore imply, for every finite $B$, that the
probability either executed control has variation at most $B$ tends to
zero. In particular there is no bounded-variation budget in the limit.
Cauchy–Schwarz on $[0,R]$ gives the same divergence in probability for the
additional quadratic energy, since $A^{-1}$ has a positive lower bound.
This does not identify that norm with physical energy or price the added
capabilities. No such capability follows from bare FIB or from a covariance
table; the conclusion is existence under the explicit finite-sign and
coefficient-access premise, with convergence and tails proved from it.

For $A=I_2$ and constant $\rho$, the limiting law is exactly K's reference
law with zero added area drift; only its finite approximating law differs.
For constant $A$ with $a^{12}\ne0$ and constant $\rho$, (29.10) still has
area drift $a^{12}$ and actual $\beta$ drift $-a^{12}/r$. Omitting the
half-product on a chord would fail that full-law comparison. Multiplying
$\rho$ by a positive constant leaves $d$ and the command laws unchanged,
while scaling $\Gamma$ inversely, so $\Gamma\,d\mu$ is unchanged as required
by unit-source occupation.

The general stochastic tools are classical. In particular [W. Whitt,
*Proofs of the martingale FCLT*, arXiv:0712.1929v2](https://arxiv.org/html/0712.1929v2),
Theorem 3.7 supplies the bounded-jump tightness criterion; Theorem 5.3 supplies
martingale preservation under uniform integrability; Theorem 5.2 supplies
Lévy's Brownian characterization. Here stopped coordinate martingales have
jumps $O_K(\sqrt\delta)$, brackets with modulus $O_K(|t-s|+\delta)$,
and bounded finite-horizon second moments, exactly the hypotheses used.
Its deterministic-bracket Brownian FCLT is not applied to a process with
state-dependent bracket. The Taylor/martingale argument above is the
classical diffusion-approximation mechanism, not a new general limit theorem.
The native lift, guards and cemetery continuity are reused from N and K;
the raw full Green and the all-start absorbing identification are reused
from §1 and the free-diffusion supplier. The additional application is the
explicit full-coefficient lawful family, its same-history enhanced lift,
and the uniform lifetime estimate closing complete Green occupation.

This gives a mathematical propagation realization beyond local dimension
selection and the existing stability classification. The path correspondence
retains the common trajectory, chronological area and death flag; K's
area variants show why first-level laws alone do not determine that joint
object. No minimal sensor or archive contract is inferred.
[Future-response sufficiency, §57](RECURSIVE_RELATIONAL_OBSERVATION_FUTURE_RESPONSE_SUFFICIENCY.md)
retains its distinct ideal response and acquisition limits; no sensor bridge
is supplied here. [Continuation X, §§264–269](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_X.md)
retains its actual-tree predictive obstruction; trees are not identified
with this cylinder. The actual-cap and near-critical results above and in
[the spatial-cap companion](FIB_NATIVE_SPATIAL_CAP_RETAINED_AND_RESONANT_LIMITS.md)
are unchanged. No simultaneous mesh/cap limit, physical spatial-dimension
selection, atomic-to-cylinder identification or priority claim is made.
These are ordinary mathematical proofs, with no Lean/kernel certification.

## 追加锚（本行以下为增补区）
