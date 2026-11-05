# Native asymptotic steering action on the original signed phase source

## 74. Native action in the complete original phase lift

**Definition 74.1 (the fixed source and the action being minimized).**
Retain [Quantitative Bounds §§69–73](FIB_NATIVE_LONG_TIME_PHASE_QUANTITATIVE_BOUNDS.md),
including its aliases G, D and N and Definitions 69.1–69.2, with one fixed
nonzero signed $\kappa$, immutable INITIAL $=(k_0,y_0)$, $k_0\in I=(l,u)$, all original preparation
phases, and the negative amplitude convention. Abbreviate

$$
c(k)=\widehat c_\kappa(k),\quad \mu(dk)=\phi(k)^2dk,\quad
M=\widehat M_\kappa=\int_I c(k)c(k)^{\mathsf T}\mu(dk),\quad
n=(2,-2,1)^{\mathsf T}.
\tag{74.1}
$$

Thus $\mu(I)=1$, $M>0$, and the rational coefficient formulas of G (25.4)
give $n^{\mathsf T}c(k)=1$. The coefficient extends continuously to
$[l,u]\Subset\mathcal J_\kappa$. Here $y=(\theta,v,D)$ always denotes
the complete real lift, with original $D$, rather than $D/\kappa$ or
wrapped endpoints. A target velocity below is denoted $w$ to distinguish
it from the second phase coordinate $v$.

For a relative command $(a,b)$ beginning at zero, exact execution means

$$
K_t=k_0+a(t),\qquad Y_t-y_0=\int_0^t c(K_s)\dot b(s)ds,\qquad
\mathsf E(a,b)=\int_0^T\{\dot a(s)^2/\varepsilon^2+\dot b(s)^2\}ds.
\tag{74.2}
$$

All times are original elapsed times starting before installation.
The declared action is precisely $\mathsf E$, without a factor $1/2$.
The killed reference retains both absorbing faces; its Q law is the
inherited Doob transform on $I$.
A command promised to remain in $I$ is an own deterministic history;
it is not a realization or reweighting of either stochastic law.
The source extrema guard in Assumption 69.2 remains mandatory at every
prefix. Phases and the relative $b$ coordinate are accumulated at joins.
Returning $a(T)=0$ below returns the height, not the phase or INITIAL.

**Assumption 74.2 (finite numerical services and an asymptotic resource
regime).** Use the certified known calibration and exact numerical
execution premises of 69.1–69.2. Admit finite rational P/Q command tapes,
including holds, and arbitrarily large finite quotas for their preparation,
records and execution. For the attainability assertions take positive
fixed lower bounds on the four service throughputs and finite fixed upper
bounds on installation overhead $t_0$ and transition latency $\ell$.
The guaranteed lower and upper service bounds are known to the scheduler.
These are a sufficient resource regime inside the stage-dependent
contracts of 69.2, not a consequence of the source or its Q law.
For each fixed requested calibration accuracy its certified computation
and storage bounds are finite; no uniform rate in that accuracy is assumed.
Target approximations used by a tape are supplied as finite rational data.
The controller is not required to compute an exact optimum or read an
unknown real target. All installation, loading and latency time is paid
by scheduled rational holds. With no random bits needed, preparation using
$U$ bit operations, $L$ peak bits and $N$ loaded timed pieces has sufficient
installation and total energy quotas of the same accounting form as
(70.5)–(70.6):

$$
\iota\ge t_0+U/r_{\rm cpu}+L/r_{\rm write}+N/r_{\rm load},\qquad
E_*\ge\mathsf E+E_0+e_{\rm cpu}U+e_{\rm write}L+e_{\rm load}N
                  +(p_0+p_{\rm mem}L)T.
\tag{74.3}
$$

The bit operations include calibration, scheduling and writing the tape;
every latency hold also remains in $T$. No common finite energy or storage
quota across horizons is required. Earlier Stop preserves lawfulness,
not the endpoint target.

**Definition 74.3 (finite infima and asymptotic meanings).** For integer
$T\ge1$ let $\mathcal N_T$ be the finite rational tapes of 74.2 with total
original duration exactly $T$, $K_T=k_0$, and $K_t\in I$ for every prefix.
Sufficient service quotas are part of each tape's contract. Define

$$
W_T=(Y_T-y_0)/T,\qquad
G_T=T^{-1}\int_0^T c(K_t)c(K_t)^{\mathsf T}dt,\qquad
A_T(w,\eta)=\inf_{\substack{(a,b)\in\mathcal N_T\\|W_T-w|<\eta}}
                  \mathsf E(a,b)/T,
\tag{74.4}
$$

with empty infimum $+\infty$, Euclidean vector norm, and operator matrix
norm. An asymptotically attaining family has $W_T\to w$ and convergent
normalized action, along integer horizons. We also consider arbitrary
sequences of finite tapes with $T_j\to\infty$. No exact finite endpoint
or finite minimum is implicit in these conventions. Horizons index
alternative finite histories from the same INITIAL, without requiring
nested tapes or permitting resets within a history.

## 75. The unrestricted native steering action

**Theorem 75.1 (exact action with finite rational native attainment).**
Under 74.1–74.3 set

$$
B=\operatorname{conv}\{\pm c(k):k\in[l,u]\},\qquad
\gamma_B(w)=\inf\{r\ge0:w\in rB\}.
\tag{75.1}
$$

Then $B$ is a full-dimensional compact centrally symmetric convex body,
$\gamma_B$ is a norm, and

$$
\lim_{\eta\downarrow0}\liminf_{T\to\infty}A_T(w,\eta)
=\lim_{\eta\downarrow0}\limsup_{T\to\infty}A_T(w,\eta)
=\gamma_B(w)^2.
\tag{75.2}
$$

Every sequence with $W_{T_j}\to w$ has
$\liminf_j\mathsf E/T_j\ge\gamma_B(w)^2$.
There is a family in $\mathcal N_T$, for every sufficiently large integer
$T$, with $W_T\to w$ and $\mathsf E/T\to\gamma_B(w)^2$.
Consequently the infimum of sequence liminf actions and the infimum of
sequence limsup actions both have this value. These are statements of
approximate velocity attainment; they do not assert exact $W_T=w$.

Proof. Positivity of $M$ implies that $c(I)$ spans $\mathbb R^3$:
a vector annihilating that span would have zero $M$ quadratic form.
Compactness of $c([l,u])$ and finite-dimensional convexity make $B$
compact. The symmetric convex hull of three independent columns contains
a neighbourhood of zero. Thus its gauge is a finite continuous norm.
The familiar support/gauge correspondence, here used only inside this
native proof, gives

$$
h_B(p)=\max_{k\in[l,u]}|p^{\mathsf T}c(k)|,\qquad
\gamma_B(w)=\max_{h_B(p)\le1}p^{\mathsf T}w.
\tag{75.3}
$$

For every actual history in (74.2), even allowing simultaneous absolutely
continuous P/Q controls, Cauchy–Schwarz in the full elapsed interval gives

$$
|p^{\mathsf T}W_T|
\le h_B(p)\left(T^{-1}\int_0^T\dot b(t)^2dt\right)^{1/2},
\qquad \mathsf E/T\ge\gamma_B(W_T)^2.
\tag{75.4}
$$

Holds have zero derivatives, but their durations remain in this inequality.
Continuity proves the sequence lower bound. If $\gamma_B$ has Euclidean
Lipschitz constant $C$, it also gives
$A_T(w,\eta)\ge(\gamma_B(w)-C\eta)_+^2$ uniformly in $T$.

Here is the construction in the actual command domain. If $w\ne0$, put
$r=\gamma_B(w)$. A finite convex combination for the boundary point
$w/r\in B$ gives, with at most four terms,

$$
w=\sum_{i=1}^q\beta_i c(s_i),\quad s_i\in[l,u],\quad
\sum_i|\beta_i|=r,\quad
\lambda_i=|\beta_i|/r,\quad d_i=r\operatorname{sgn}(\beta_i).
\tag{75.5}
$$

Indeed choose signed atoms in a convex representation; the displayed
coefficients have total absolute value $r$. Zero weights are omitted.
Ideal dwelling a fraction $\lambda_i$ at $s_i$ with $\dot b=d_i$ gives
velocity $w$ and phase action rate $\sum_i\lambda_i d_i^2=r^2$.
This convex-design intermediate is the Elfving geometry credited in 78.1;
it does not supply the following native execution.

For each accuracy index $j$, replace $s_i$ by
$k_i=k_0+q_i\in I$, $q_i\in\mathbb Q$, approaching $s_i$ from the
interior, replace the positive weights by positive rational weights
$\lambda_i'$ summing to one, and replace $d_i$ by rationals $d_i'$.
Continuity gives finite designs with

$$
\nu_j=\sum_i\lambda_i'c(k_i)d_i'\longrightarrow w,
\qquad e_j=\sum_i\lambda_i'(d_i')^2\longrightarrow r^2.
\tag{75.6}
$$

Only these rational inputs, not the real quantities in (75.5), are issued.
Existence of such inputs for every real target is an approximation claim,
not an operation discovering that target. Certified calibration supplies
strict interior margins and finite enclosures of the required coefficients.
The dense height set $k_0+\mathbb Q$ works even for irrational $k_0$;
no absolute rational height or read of $k_0$ is assumed.

Fix one such rational design. Visit its heights in increasing order,
starting at $k_0$ and finally returning to $k_0$. Every height displacement
is rational. Give every nonzero P move one unit of original time, with
$\dot b=0$, and reserve a rational latency hold at each join. The total
height variation is at most $2(u-l)$ and its action is at most
$4(u-l)^2/\varepsilon^2$. The number and duration of these moves and
latency holds are finite constants for this fixed design. Each segment
stays between its endpoint heights, hence strictly in $I$, including the
last return. Holds also stay there. The extrema therefore satisfy the
original strict $\mathcal J_\kappa$ guard, not just an endpoint test.

The horizon-dependent tape uses $O_j(1+\log T)$ bits: its only growing
numbers are rational durations and displacements with fixed denominators
and numerators of size $O_j(T)$. Elementary rational arithmetic writes
and loads it in $O_j((1+\log T)^{q_j})$ bit operations for some finite
integer $q_j$. Fixed-accuracy calibration has a finite additional cost.
Positive fixed throughputs therefore allow an integer installation hold
bounded by $C_j(1+\lceil\log_2(T+1)\rceil)^{q_j}$, after increasing
$C_j,q_j$ if necessary. This pays (70.5), with no fair bits needed.
Together with travel and latency, let its total non-dwell time be $D_j(T)$.
Then $D_j(T)/T\to0$, with all time still on the original clock.

For $T>D_j(T)$ set $S=T-D_j(T)$ and dwell for exactly the rational
duration $S\lambda_i'$ at $k_i$, with rational phase speed $d_i'$.
The issued Q displacement $S\lambda_i'd_i'$ is rational. Heights do not
move during Q, and all control increments are translated at joins as in
N Theorem 9.2. The full real lift, not only its torus class, consequently
satisfies

$$
W_T=(S/T)\nu_j,\qquad
\mathsf E/T=(S/T)e_j+E_{P,j}/T,
\quad 0\le E_{P,j}\le4(u-l)^2/\varepsilon^2.
\tag{75.7}
$$

This includes installation, holds and the final height return.
Choose increasing integer thresholds $T_j\ge j$ such that for this fixed
design the differences $|W_T-\nu_j|$ and $|\mathsf E/T-e_j|$
are at most $1/j$ whenever $T\ge T_j$.
Use design $j$ for $T_j\le T<T_{j+1}$. This diagonal family attains the
claimed limits. It also provides $\limsup_T A_T(w,\eta)\le r^2$ for
every $\eta>0$. The uniform lower bound proves (75.2).
For $w=0$ the stationary all-hold tape gives zero action and velocity.
All service quotas are finite at each stage; (74.3) pays their separate
charges. No service charge has been identified with $\mathsf E$. $\square$

## 76. Exact comparison with the existing transport covariance

**Theorem 76.1 (the native face, contacts and equality velocities).**
For the same source define the covariance ellipsoid
$E_M=\{w:w^{\mathsf T}M^{-1}w\le1\}$. Then

$$
E_M\subset B,\qquad
B\cap\{w:n^{\mathsf T}w=1\}
 =\operatorname{conv}c([l,u]),\qquad n^{\mathsf T}Mn=1.
\tag{76.1}
$$

The displayed exposed face has affine dimension two. The entire contact
set and all equality velocities are

$$
\partial E_M\cap\partial B=\{Mn,-Mn\},\qquad
\gamma_B(w)^2\le w^{\mathsf T}M^{-1}w,
\quad \text{equality}\ \Longleftrightarrow\ w\in\mathbb R Mn.
\tag{76.2}
$$

In particular the unrestricted asymptotic action is not a positive
definite quadratic form. The autonomous covector line in original
coordinates is $\mathbb R n$; the action equality velocity line is
$\mathbb R Mn$, related by the covariance map rather than identified
by equality of coordinate dimension.

Proof. Since $n^{\mathsf T}c=1$, the signed atoms have $n$ readings
$+1$ and $-1$. A convex combination has reading one precisely when it
uses only positive atoms. This proves the face formula. Its affine
hull has dimension at most two; if it had dimension at most one, the
linear span of $c([l,u])$ would have dimension at most two, contradicting
$M>0$. Thus the face is nontrivial and two-dimensional. Also
$n^{\mathsf T}Mn=\int_I(n^{\mathsf T}c)^2d\mu=1$.

The support function of $E_M$ is $\sqrt{p^{\mathsf T}Mp}$ and

$$
p^{\mathsf T}Mp=\int_I(p^{\mathsf T}c(k))^2\mu(dk)\le h_B(p)^2.
\tag{76.3}
$$

The support inequalities imply inclusion. For nonzero $p$, equality
in (76.3) forces $(p^{\mathsf T}c(k))^2$ constant on $[l,u]$, since
$\phi^2$ is positive throughout $I$ and the integrand is continuous.
Connectedness then makes $p^{\mathsf T}c(k)$ constant, including the
zero case. D Theorem 50.1, transferred by its exact signed dual map
$\eta=(p_1,p_2,\kappa p_3)$, says precisely $p\in\mathbb R n$.
Conversely that line gives equality. This reuses its exhaustive rational
coefficient classification, not just its sufficient character identity.

If $x\in\partial E_M\cap\partial B$, choose a nonzero supporting
covector $p$ of $B$ at $x$. Since $x\in E_M\subset B$, both supports
coincide at $x$. Hence $p\in\mathbb R n$, and the unique ellipsoid
support point $Mp/\sqrt{p^{\mathsf T}Mp}$ is $Mn$ or $-Mn$.
Both points do lie in the common boundary by (76.1). Radial normalization
now proves (76.2) for every nonzero $w$, and zero also gives equality.
A positive definite quadratic unit ball is strictly convex, whereas $B$
has the face just proved; thus $\gamma_B^2$ is not such a quadratic form.
Finally $Mn=\int_I c\,d\mu$, while $n$ acts on phase displacements.
D Theorem 50.1 classifies these covectors, not steering velocities.
No claim that $M$ is a scalar multiple of the original metric is used.
$\square$

## 77. Prescribing the empirical Gram matrix

**Definition 77.1 (an additional occupation condition).** Impose on the
actual finite histories, over the whole clock including all holds,

$$
G_{T_j}=T_j^{-1}\int_0^{T_j}c(K_t)c(K_t)^{\mathsf T}dt\longrightarrow M.
\tag{77.1}
$$

Let $A_T^M(w,\eta)$ be (74.4) with the additional requirement
$\|G_T-M\|<\eta$. This condition concerns deterministic command occupation.
It is not supplied by numerical execution, by the raw killed law, or by
the fact that the Q law has invariant density $\phi^2$. Condition (77.1)
is weaker than prescribing the entire empirical height measure.

**Theorem 77.2 (occupation-restricted action and native attainability).**
Under 74.1–74.3 and (77.1), every sequence with $W_{T_j}\to w$ has
$\liminf_j\mathsf E/T_j\ge w^{\mathsf T}M^{-1}w$. There is a family of
finite rational native tapes, returning to $k_0$ at every sufficiently
large integer horizon, with

$$
W_T\to w,\qquad G_T\to M,\qquad
\mathsf E/T\to w^{\mathsf T}M^{-1}w.
\tag{77.2}
$$

Moreover

$$
\lim_{\eta\downarrow0}\liminf_{T\to\infty}A_T^M(w,\eta)
=\lim_{\eta\downarrow0}\limsup_{T\to\infty}A_T^M(w,\eta)
=w^{\mathsf T}M^{-1}w.
\tag{77.3}
$$

The infima of liminf and limsup actions over sequences satisfying both
limits also equal this value. Equality of this restricted value with
the unrestricted value occurs exactly for $w\in\mathbb R Mn$.

Proof. For any constant covector $p$, positivity of a square gives the
finite-history inequality

$$
\mathsf E/T\ge 2p^{\mathsf T}W_T-p^{\mathsf T}G_Tp.
\tag{77.4}
$$

It follows by expanding $T^{-1}\int_0^T(\dot b-p^{\mathsf T}c(K))^2dt$
and adding the nonnegative height action. For $G_T>0$, maximizing over
$p$ gives $\mathsf E/T\ge W_T^{\mathsf T}G_T^{-1}W_T$.
In a convergent sequence use $p=M^{-1}w$ in (77.4) to obtain the claimed
lower bound without assuming invertibility at early stages. For the
finite infima, that same $p$ gives the uniform lower bound
$w^{\mathsf T}M^{-1}w-2|p|\eta-|p|^2\eta$.

For attainment, take finite positive rational weights $\lambda_i$ summing
to one and heights $k_i=k_0+q_i\in I$, $q_i\in\mathbb Q$, whose empirical
probabilities converge weakly to $\mu$. Such quadratures exist: partition
$[l,u]$ into shrinking cells, choose an interior dense-set node in every
nonempty cell, approximate their $\mu$ masses by positive rationals and
renormalize. Uniform continuity of each entry of $cc^{\mathsf T}$ gives

$$
M_j=\sum_i\lambda_i c(k_i)c(k_i)^{\mathsf T}\longrightarrow M.
\tag{77.5}
$$

In particular $M_j>0$ eventually. At fixed stage the ideal dwell speeds
$d_i=c(k_i)^{\mathsf T}M_j^{-1}w$ give exactly

$$
\sum_i\lambda_i c(k_i)d_i=w,\qquad
\sum_i\lambda_i d_i^2=w^{\mathsf T}M_j^{-1}w.
\tag{77.6}
$$

Choose rational speeds $d_i'$ so their maximal error tends to zero.
This can be done from finite target approximations and certified source
enclosures, since positive definiteness can be certified with a strictly
positive rational eigenvalue bound. No exact real inverse is executed.
Boundedness of $c$ and of $M_j^{-1}$ makes these speeds uniformly bounded
for fixed $w$ and sufficiently large $j$. Thus the velocity and phase
action rate in (77.6) converge to $w$ and $w^{\mathsf T}M^{-1}w$ after
rational replacement. The case $w=0$ uses zero dwell speeds.

Apply the full native schedule of the proof of 75.1 to each such finite
design: sorted rational height moves, rational latency holds, paid
installation, dwell, and final return. For fixed $j$, the number of
nodes is finite; its source precision cost need not have any bound
uniform in $j$. Choose $T$ sufficiently large to pay that cost and the
$O_j((1+\log T)^{q_j})$ tape cost with $D_j(T)/T\to0$. All prefixes
remain in a certified compact subinterval of $I$. Let $C_c=\max_{[l,u]}|c|$.
On the entire original interval the Gram matrix satisfies

$$
G_T=(S/T)M_j+R_{j,T},\qquad
\|R_{j,T}\|\le C_c^2 D_j(T)/T,
\quad S=T-D_j(T).
\tag{77.7}
$$

Indeed the dwell contribution is exactly the first term, and every
installation, transition, P-travel or terminal interval contributes at
most its duration times $C_c^2$. No such interval is removed from time
or treated as having zero Gram contribution. The height action remains
bounded by $4(u-l)^2/\varepsilon^2$.
Choose a subsequence of designs whose three limiting errors are at most
$1/j$. Choose increasing thresholds so the deviations from each fixed
design are at most $1/j$ for all later integer $T$, and diagonalize
as in 75.1. Equations (77.5)–(77.7) prove (77.2). Combining this upper
construction with (77.4) proves (77.3) and the sequence statements.
The last assertion is exactly the contact consequence (76.2). $\square$

## 78. The source correspondence and its mathematical boundary

**Definition 78.1 (attributed intermediates and the native inference).**
The convex-design ingredient in (75.5) is classical Elfving geometry:
G. Elfving, *Optimum Allocation in Linear Regression Theory*, Annals of
Mathematical Statistics 23, 255–262, DOI
[10.1214/aoms/1177729442](https://doi.org/10.1214/aoms/1177729442).
An accessible original research exposition is G. Sagnol, *Computing Optimal
Designs of multiresponse Experiments reduces to Second-Order Cone
Programming*, [arXiv:0912.5467v1, §2, Theorem 2.1](https://arxiv.org/html/0912.5467v1#S2).
Its regression vector $a_x$ is $c(k)$, its design weights are height dwell
fractions, its estimand is $w$, and its Elfving set is $B$.
Its relation $tw=\sum_i\lambda_i\epsilon_i a_{x_i}\in\partial B$
with variance $t^{-2}$ gives the convex-design value $\gamma_B(w)^2$.
This is an attributed intermediate, not a new convex-duality theorem.
The source-free finite-atom gauge and support results are also already
present in [Recovery geometry, Theorem 5.2 and Corollary 5.3](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md).
They are not independently new conclusions here.

Theorems 75.1–77.2 are `repo-derived` ordinary mathematical consequences
for the signed source (69.1), with the exact-execution and resource
premises 74.2. Their additional content is the guarded rational
original-clock realization and return, the two-dimensional face and
exhaustive covariance contacts obtained using D Theorem 50.1, and native
attainment under the independently imposed empirical Gram condition.
The tensor used throughout is precisely the $\widehat M_\kappa$ of
69.1 and 72.1, not the resolved-coordinate $M_\kappa$ of D §36.
The norm comparison therefore connects the existing transport consumer
to operations on its own source, without a whitening or $D/\kappa$ change.

**Proposition 78.2 (what the action comparison supplies to a same-source
geometry contract).** With the horizontal cost and exact native execution
fixed as in 74.1–74.2, the transport covariance does not by itself give
the unrestricted steering action $w^{\mathsf T}M^{-1}w$: it does so only
on $\mathbb R Mn$. Imposing (77.1) gives that quadratic action in all
three directions. Neither alternative alone supplies the old-distance
identification or the source-to-base field and guard descent required
by [Observer §16](AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md). Service energy is also not determined by either action.

Proof. Theorems 75.1 and 76.1 give strict inequality away from the stated
line; 77.2 gives equality of the occupation-restricted value with the
quadratic form. The unrestricted ball has a two-dimensional face, so
it cannot be any positive definite quadratic distance ball on this
three-dimensional lift. A prescribed occupation changes the admissible
histories; it is an additional constraint, not a consequence of matching
transport rank or of an invariant measure of a different law.
Observer Assumption 16.1 and Theorems 16.2–16.4 require an actual distance
law, descended fields, complete lawful lifts and matching source/base
lifetimes. None of these is an assumption or conclusion of (75.2),
(76.2) or (77.3), which concern this source's original phase lift.
Finally (74.3), like (70.6), includes the separate term
$(p_0+p_{\rm mem}L)T$ and the operation tariffs. For example increasing
$p_0$ adds a nonzero cost per unit time while leaving $c,M$ and both
horizontal action formulas unchanged. Thus those formulas characterize
only the declared horizontal action, even when all service charges are
paid. They assert no physical identification, fixed-resource attainment,
zero-leaf extension, command-error robustness or Lean certification.
$\square$

## 追加锚（本行以下为增补区）
