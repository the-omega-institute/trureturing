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
