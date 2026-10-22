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
