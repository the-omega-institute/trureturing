# Same-source native attractive boundary response

## 1. The fixed source and the completed mixed realization

**Definition 1.1 (source, clock, measures and coupling interval).** Write
C for [Native central-noise Green stability](FIB_NATIVE_CENTRAL_NOISE_GREEN_STABILITY.md)
and V for [Variable-coefficient Green stability](FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md),
with their statements as present at revision
5cec4fa83ae7bbb4e787c42606525db4cd11ed48. Retain C, Definitions
1.1–1.2 and 15.1: $r=1-Z>0$, $0<l<k_o<u<r/2$,
$\Omega=(l,u)\times\mathbb T^2$, both actual periods $2\pi$, the
original preparation phases and interior pole $o$. Put

$$
\begin{aligned}
 d\mu&=dk\,d\alpha\,d\beta,&d\sigma&=d\alpha\,d\beta,\\
 P&=\partial_k,&Q&=\tfrac12\partial_\alpha+(\tfrac12-k/r)\partial_\beta,
 &Z_c&=-r^{-1}\partial_\beta,\\
 T_\epsilon[v]&=\|Pv\|_2^2+\|Qv\|_2^2+\epsilon^2\|Z_cv\|_2^2,
 &\mathscr H&=L^2(\Omega,d\mu;\mathbb C),
 &\mathscr K&=L^2(\mathbb T^2,d\sigma;\mathbb C).
\end{aligned}
\tag{1.1}
$$

Pairings are linear in the first argument. For every $\epsilon\ge0$,
$\Gamma_{\epsilon,o}$ is the ORIGINAL both-face killed FREE Green
field, relative to $d\mu$, for $L_\epsilon$ and its covariance-$2$
clock $e^{-tL_\epsilon}$. In particular the potential is neither the
mixed Green field nor a Green field regenerated in a smaller slab.
Set $h_I=u-l$ and, with C, Definition 16.2,

$$
 m_0=(2r)^{-1},\qquad g_*=m_0\Lambda_*,\qquad
 g_{\mathrm c}=2\pi m_0\lambda_0,\qquad 0<g_*\le g_{\mathrm c}.
\tag{1.2}
$$

Fix a finite $\epsilon_0\ge0$. All uniform assertions below range over
$0\le\epsilon\le\epsilon_0$, $0\le g\le g_*$. They do not assume
$g_*=g_{\mathrm c}$. The expression
$q_{\epsilon,g}=T_\epsilon-g\int\Gamma_{\epsilon,o}|v|^2d\mu$
is initially defined on the free mixed domain $\mathcal V_\epsilon$
of C, Definition 31.1 (zero upper trace, unrestricted lower trace).
Its closure is denoted $q^M_{\epsilon,g}$ with domain $\mathcal D^M$.
The both-zero-trace closure is $q^D_{\epsilon,g}$, with domain
$\mathcal D^D$. These are analytic attractive forms; no new stochastic
law, boundary actuator or admissible command is part of this definition.

**Theorem 1.2 (uniform shifted realization and its actual trace).** There
is a finite $B\ge0$, depending only on the fixed geometry, pole,
$\epsilon_0$ and $g_*$, such that both closures in Definition 1.1 exist
and, for all $s\ge s_0:=B+1$,

$$
 A_s[v]:=q^M_{\epsilon,g}[v]+s\|v\|_2^2\ge\|v\|_2^2.
\tag{1.3}
$$

The associated selfadjoint operators $H^M_{\epsilon,g}$ and
$H^D_{\epsilon,g}$ are the mixed and killed attractive Friedrichs
realizations. For $\epsilon>0$, or for $\epsilon=0$ and
$g<g_{\mathrm c}$, their form domains are the corresponding free
mixed and free killed domains. If $\epsilon=0$ and
$g=g_{\mathrm c}$ is in the interval under consideration, their domains
are instead the ground-transform completions described below. The
lower trace extends continuously to $\mathcal D^M$ and satisfies

$$
 \gamma_l\mathcal D^M=\mathcal T_{\epsilon,s},\qquad
 \ker\gamma_l=\mathcal D^D.
\tag{1.4}
$$

Here $\mathcal T_{\epsilon,s}$ is exactly the FREE weighted trace
domain of C, (31.3), including its horizontal meaning at zero noise.
The bulk form domains are compactly embedded in $\mathscr H$ for each
fixed pair $(\epsilon,g)$. No uniform equivalence with the free bulk
energy is claimed.

Proof. C, Theorem 16.3 supplies a common lower bound $-B_D$ for the
killed forms at $g=g_*$ and $0<\epsilon\le\epsilon_0$; if
$\epsilon_0=0$, use any auxiliary positive upper noise bound to define
$B_D$. Monotonicity in $g$ gives the same bound for smaller couplings.
The bound also holds on the zero-noise smooth core. Indeed the kinetic
energies converge there, and the potential integrals converge by C,
Theorem 3.1, its local homogeneous bound and the uniform integrability
of $R^{-2}$ against a bounded smooth test and raw volume $O(R^3dR)$.
Equivalently C, (17.4), supplies the required uniform small-ball mass.
Thus this limiting argument uses the entire field, not only its tangent.

Choose real smooth height cutoffs $\chi,\zeta$ with
$\chi^2+\zeta^2=1$, $\chi=1$ near $k_o$, $\chi=0$ near both height
faces, and $\zeta=0$ near $k_o$, $\zeta=1$ near both faces. By C,
Proposition 15.2, the following finite numbers exist:

$$
 K=\sup_{0\le\epsilon\le\epsilon_0}
       \|\Gamma_{\epsilon,o}\|_{L^\infty(\operatorname{supp}\zeta)},
 \qquad J=\|\chi'^2+\zeta'^2\|_\infty.
\tag{1.5}
$$

The classical IMS product identity, applied to these height cutoffs,
gives on the mixed core

$$
 q_{\epsilon,g}[v]
 =q_{\epsilon,g}[\chi v]+q_{\epsilon,g}[\zeta v]
       -\int(\chi'^2+\zeta'^2)|v|^2d\mu
 \ge T_\epsilon[\zeta v]-B\|v\|_2^2,
 \quad B:=B_D+g_*K+J.
\tag{1.6}
$$

Increase $B_D$ to be nonnegative if necessary. Since $\chi v$ has both
zero outer traces, the killed lower bound applies. This proves not
only (1.3) but the stronger estimate

$$
 A_s[v]\ge T_\epsilon[\zeta v]+\|v\|_2^2.
\tag{1.7}
$$

For fixed positive noise the infinitesimal free-form potential bound
in C, Theorem 4.1, localizes by the same cutoffs to the mixed domain;
the exterior multiplier is bounded. KLMN therefore gives closure on
exactly $\mathcal V_\epsilon$. At zero noise below $g_{\mathrm c}$,
V, (13.2)–(13.3), with the same localization gives the free mixed
domain and norm equivalence for each fixed subcritical $g$.

Here is the precise endpoint correspondence. In V, (10.1)–(10.2),
set $A=I_2$, $\rho=1$. Its chart is C, (15.1), its raw density is
exactly $m_0=(2r)^{-1}$, its horizontal fields are $(U,V)$, and its
free killed field at zero noise is exactly $\Gamma_{0,o}$. Its critical
coupling is consequently (1.2), with no Jacobian or clock adjustment.
Let $H$ equal $R^{-1}\phi(a)$ near the pole and equal one outside a
compact interior chart, as in V, Definition 12.1. For the mixed case put

$$
\begin{aligned}
 \mathcal W_H^M&=\overline{\{v:\ v\text{ smooth periodic, zero at }u,
                    \text{ and zero near }o\}}
 ^{(\int H^2|v|^2d\mu+\int H^2(|Pv|^2+|Qv|^2)d\mu)^{1/2}},\\
 \mathcal D^M&=H\mathcal W_H^M,\qquad
 \overline q^M_{0,g_{\mathrm c}}[Hv]
 =\int H^2(|Pv|^2+|Qv|^2)d\mu+\int W|Hv|^2d\mu,\\
 W&=H^{-1}L_0H-g_{\mathrm c}\Gamma_{0,o}.
\end{aligned}
\tag{1.8}
$$

The corresponding killed space uses zero values at both faces. The
completion has no hidden boundary condition at the pole. The frozen
angular equation of V, (12.4), cancels its $R^{-2}$ singularity exactly.
In this constant-coefficient model C, (3.2), even makes $W$ bounded
near the pole; it is bounded elsewhere as well. The ground identity
on the punctured core thus proves closability and identifies (1.8).
V, Theorem 12.2, proves that the original free killed domain has this
same completion. Its proof is local at the pole, so it also applies
with a free lower face: $H=1$ near both faces, and exterior approximation
is the ordinary mixed horizontal approximation of C, (31.1).
In particular the completed domain is strictly larger than the free
domain at this endpoint, by V's compactly supported witness $\chi_0H$.
Separate kinetic and potential integrals need not be finite there;
(1.8) is the form value, not a subtraction of infinities.
This identifies the closure of the original free mixed form as well.
The estimates (1.6)–(1.7) extend by completion.

For the trace, (1.7) makes $\zeta v$ a free mixed member and
$\gamma_l v:=\gamma_l(\zeta v)$ continuous into the free trace-energy
space. This definition agrees with every original smooth trace and is
independent of the cutoff, since cutoffs equal one in a lower collar.
It proves one inclusion in (1.4). Conversely, for
$f\in\mathcal T_{\epsilon,s}$, the free lift
$w=\mathcal P_{\epsilon,s}f$ belongs to $\mathcal V_\epsilon$ and hence
to $\mathcal D^M$, so every such trace occurs.
For the kernel identification, choose a smooth lower-collar cutoff
$\tau=1$ at $l$, supported away from the pole and from $u$.
The map $E f=\tau\mathcal P_{\epsilon,s}f$ is bounded from the free
trace-energy norm into $A_s$: the product rule, C, (32.2), and boundedness
of the potential on this collar prove this assertion. If $v_j$ are mixed
core approximants to a trace-zero $v$, then
$v_j-E\gamma_l v_j\to v$ in $A_s$. Each difference has zero traces,
belongs to the free killed domain, and can be approximated by its
punctured killed core. Thus $v\in\mathcal D^D$. The reverse inclusion
is trace continuity. This also proves that $q^D$ is the restriction of
$q^M$ to this kernel, including the completed case.

For completeness the free mixed compactness at zero noise follows
directly from C, (31.1), without a boundary ellipticity premise. For a
normalized modal function $v(h_I)=0$, write
$E=\int(|v'|^2+(a-bx)^2|v|^2)dx$ and $t=|b|>0$. Its squared supremum
is at most $2\sqrt E$. The set $|a-bx|\le\sqrt t$ has length at most
$2/\sqrt t$, and outside it the potential is at least $t$. Hence
$1\le4\sqrt{E/t}+E/t$, which implies $E\ge t/25$. For bounded $n$
and unbounded $m$, the potential minimum tends to infinity instead.
Thus modal lower energies diverge off finite lattice sets. Finite-mode
$H^1$ compactness and this tail estimate prove the free mixed compact
embedding, also at positive noise by energy domination. At the critical
pole use V, Theorem 12.2's small-source-mass estimate and its exterior
compactness argument; neither argument uses the lower Dirichlet
condition. This proves compactness of (1.8). The closed-form
representation theorem supplies precisely the asserted operators.
The IMS and KLMN steps are the classical intermediate form results in
Teschl, [*Mathematical Methods in Quantum Mechanics*, public edition,
Theorem 6.24 and Lemma 11.3](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf); the source correspondence and boundary domain
identifications above are necessary additional native steps. $\square$

## 2. Attained response and the uniform native rank law

**Definition 2.1 (attractive lower response).** For $s\ge s_0$ and
$f\in\mathcal T_{\epsilon,s}$ set

$$
 b_{\epsilon,g,s}[f]=\min_{\substack{v\in\mathcal D^M\\\gamma_l v=f}}A_s[v],
 \qquad P_{\epsilon,g,s}f=\operatorname*{argmin}_{\gamma_l v=f}A_s[v].
\tag{2.1}
$$

Polarization defines the sesquilinear form $b$. Its associated
boundary operator is $\Lambda_{\epsilon,g}(s)$ and its inverse is
$C_{\epsilon,g}(s)$. The conormal is defined variationally by
$A_s(Pf,v)=\langle\Lambda_{\epsilon,g}(s)f,\gamma_l v\rangle$ on the
operator domain. It is $-\partial_k$ at the lower face whenever the
classical derivative exists. The complex Fourier basis for all free
comparisons is $(2\pi)^{-1}e^{i(m\alpha+n\beta)}$, never the basis for
a probability-normalized torus.

**Theorem 2.2 (positive closed response, including the completed endpoint).**
Fix any finite $S\ge s_0$, and put $a_S=1/\max(1,S)$. Uniformly for
$0\le\epsilon\le\epsilon_0$, $0\le g\le g_*$ and $s_0\le s\le S$,
the minimum (2.1) is attained uniquely. Its densely defined closed
positive form has the exact domain $\mathcal T_{\epsilon,s}$ and

$$
 a_S\mathfrak l_{\epsilon,s}[f]\le b_{\epsilon,g,s}[f]
       \le\mathfrak l_{\epsilon,s}[f].
\tag{2.2}
$$

Consequently $\Lambda_{\epsilon,g}(s)$ has compact resolvent, its
inverse is bounded, positive and compact, and

$$
 \|C_{\epsilon,g}(s)\|\le h_I/a_S.
\tag{2.3}
$$

For every $F\in\mathscr K$, $w=P_{\epsilon,g,s}C_{\epsilon,g}(s)F$
is the unique mixed form member solving

$$
 A_s(w,v)=\langle F,\gamma_l v\rangle\quad(v\in\mathcal D^M).
\tag{2.4}
$$

Proof. The affine constraint is a nonempty closed affine subspace
of the Hilbert space with norm $A_s^{1/2}$. Orthogonal projection
onto its trace kernel proves attainment, uniqueness and orthogonality
to $\mathcal D^D$. The free minimum principle and (1.7) give

$$
 \mathfrak l_{\epsilon,s}[\gamma_l v]
 \le T_\epsilon[\zeta v]+s\|\zeta v\|_2^2
 \le\max(1,S)A_s[v].
\tag{2.5}
$$

For the opposite bound use the actual free minimizer in (2.1):
$q_{\epsilon,g}\le T_\epsilon$, also for the restriction of a completed
form to its original free domain. This gives the upper bound in (2.2).
It proves closedness by equivalence with the closed free trace form,
without an equivalence of bulk domains. Compactness of the free trace
embedding follows from C, Theorem 32.1's weights
$h_I^{-1}+\sqrt s+|m/2+c(l)n|+\sqrt{|n|/r}+\epsilon|n|/r$ tending to
infinity off finite lattice sets. The same holds for $b$. Its lower
bound $a_S/h_I$ proves (2.3). Orthogonality and the associated-operator
identity prove (2.4); positivity gives uniqueness. The general
trace-energy construction is the classical form method of Arendt–ter
Elst, [*The Dirichlet-to-Neumann operator on rough domains*,
arXiv:1005.0875](https://arxiv.org/abs/1005.0875). Here (1.4) and (2.5)
supply its concrete domain and coercivity instead of assuming ellipticity.
$\square$

**Theorem 2.3 (two-sided native inverse-response capacity).** Let
$d_{\epsilon,g}(\eta;s)$ be the minimum complex rank of a bounded
complex-linear map $B:\mathscr K\to\mathscr K$ such that
$\|C_{\epsilon,g}(s)-B\|\le\eta$. Let $\mu_j$ be the positive
eigenvalues of $C_{\epsilon,g}(s)$, in decreasing order with multiplicity.
Then

$$
 d_{\epsilon,g}(\eta;s)=\#\{j:\mu_j>\eta\}.
\tag{2.6}
$$

For the strict contract $\|C-B\|<\eta$, replace $>$ by $\ge$.
No finite rank attains zero error. In the parameter ranges of Theorem
2.2 take $\eta_l,K_l^-,K_l^+$ from C, (33.2), with $S_0=S$ and the
present $\epsilon_0$. For all $0<\eta\le\eta_l$,

$$
 \frac{K_l^-}{\eta^2(\eta+\epsilon)}
 \le d_{\epsilon,g}(\eta;s)
 \le\frac{K_l^+a_S^{-3}}{\eta^2(\eta+\epsilon)}.
\tag{2.7}
$$

The same constants bound the strict-contract count. These estimates
include $\epsilon=0$, $g=g_*$, all tolerance endpoints and the crossover
$\eta=\epsilon$. They concern the entire raw complex $L^2$ forcing
unit ball in operator norm.

Proof. Compact positivity gives (2.6) by the spectral truncation and
rank-nullity argument of C, Theorem 28.1; this is the classical best-rank
argument, not a new approximation theorem. Min–max in the common
trace form domain in (2.2) compares the ordered boundary eigenvalues
and hence the ordered inverse eigenvalues to their free values:
$\mu_j^{\rm free}\le\mu_j\le a_S^{-1}\mu_j^{\rm free}$.
Therefore, with precisely the same strictness at each endpoint,

$$
 d^l_\epsilon(\eta;s)\le d_{\epsilon,g}(\eta;s)
                  \le d^l_\epsilon(a_S\eta;s).
\tag{2.8}
$$

Apply C, Theorem 33.1. Since $a_S\le1$, its tolerance range includes
$a_S\eta$, and
$(a_S\eta)^2(a_S\eta+\epsilon)\ge a_S^3\eta^2(\eta+\epsilon)$.
This proves (2.7). Infinite-dimensionality and strict positivity of the
inverse exclude exact finite rank. The potential couples Fourier
modes, so no diagonal attractive multiplier is being asserted. $\square$

## 3. Bounded bulk Poisson realization and the mixed comparison

**Theorem 3.1 (a strong same-potential resolvent reconstruction).** In
Theorem 2.2's full parameter range the map $P_{\epsilon,g,s}$ extends
from its trace-energy domain to a bounded map $\mathscr K\to\mathscr H$
with one common finite bound $p_A$. With
$R^D_g(s)=(H^D_{\epsilon,g}+s)^{-1}$ and
$R^M_g(s)=(H^M_{\epsilon,g}+s)^{-1}$,

$$
 R^M_g(s)=R^D_g(s)+P_{\epsilon,g,s}C_{\epsilon,g}(s)P_{\epsilon,g,s}^*.
\tag{3.1}
$$

In particular for any bounded complex-linear $B$ on $\mathscr K$,

$$
 \|R^M_g(s)-(R^D_g(s)+P_{\epsilon,g,s}BP_{\epsilon,g,s}^*)\|
 \le p_A^2\|C_{\epsilon,g}(s)-B\|.
\tag{3.2}
$$

The exact killed inverse is retained; (3.2) is not a sharp approximation
rank theorem for the whole bulk resolvent.

Proof. The $L^2$ boundedness needs more than (2.2). Set
$p=\sqrt{h_I/3}$, and write $w=\mathcal P_{\epsilon,s}f$ for the FREE
Poisson lift, initially for a finite Fourier sum $f$. By C, (32.2),
$\|w\|_2\le p\|f\|_2$ uniformly. Choose real compactly supported
height cutoffs $\theta,\theta_1$ with $\theta=1$ near $k_o$ and
$\theta_1=1$ on $\operatorname{supp}\theta'$, both supported away from
$l,u$. Put

$$
 d_1=\|\theta'\|_\infty,\quad d_2=\|\theta''\|_\infty,
 \quad e_1=\|\theta_1'\|_\infty,\quad
 K_\theta=\sup_{\epsilon\le\epsilon_0}
 \|\Gamma_{\epsilon,o}\|_{L^\infty(\operatorname{supp}(1-\theta))}.
\tag{3.3}
$$

Take $0\le\theta\le1$ so this last supremum is away from a fixed
source neighbourhood. Testing the free harmonic equation with
$\theta^2w$ and $\theta_1^2w$ gives the exact cutoff identity
$T_{\epsilon,s}[\theta w]=\int|\theta'|^2|w|^2d\mu$ and its
$\theta_1$ counterpart. Thus

$$
 \|\theta w\|_{A_s}\le d_1p\|f\|_2,\qquad
 \|(L_\epsilon+s)(\theta w)\|_2
 \le p(d_2+2d_1e_1)\|f\|_2.
\tag{3.4}
$$

For the second inequality use
$(L_\epsilon+s)(\theta w)=-\theta''w-2\theta'Pw$;
$\theta_1=1$ on the derivative support controls $Pw$ there. The
cutoffs commute with $Q,Z_c$, so no inverse power of noise occurs.

On a punctured killed test $v$, integration by parts gives

$$
 g\int\Gamma_{\epsilon,o}\theta w\overline v\,d\mu
 =\langle(L_\epsilon+s)(\theta w),v\rangle-A_s(\theta w,v).
\tag{3.5}
$$

Here $\theta w\in\mathcal D^D$ even at the completed endpoint, and
(3.4) bounds the right side in the $A_s$ norm. The remaining potential
pairing is bounded by $g_*K_\theta p\|f\|_2\|v\|_2$. Consequently
the functional initially given on that core by
$\ell_f(v)=g\int\Gamma_{\epsilon,o}w\overline v\,d\mu$ extends to
$\mathcal D^D$, with norm at most $K_A\|f\|_2$, where one explicit
choice is

$$
 K_A=p(d_2+2d_1e_1+d_1+g_*K_\theta),\qquad p_A=p+K_A.
\tag{3.6}
$$

This continuous extension is the meaning of the pairing on a completed
domain; no separate global free-energy bound on $v$ is used. By Riesz
representation there is a unique $z\in\mathcal D^D$ with
$A_s(z,v)=\ell_f(v)$ and $\|z\|_{A_s}\le K_A\|f\|_2$.
On punctured tests the free equation gives $A_s(w,v)=-\ell_f(v)$.
Since $w\in\mathcal D^M$, both sides extend continuously, so $w+z$
is the attractive harmonic minimizer with trace $f$. Thus
$\|P_{\epsilon,g,s}f\|_2\le(p+K_A)\|f\|_2$. Finite Fourier sums
are dense both in the raw boundary space and in the free trace-energy
domain; (2.2) shows that this extension agrees with (2.1) for every
finite-energy trace. This proves the asserted bounded realization,
including the critical completion.

For $F\in\mathscr H$ set $u_D=R^D_g(s)F$,
$f=C_{\epsilon,g}(s)P_{\epsilon,g,s}^*F$, and $u=u_D+Pf$.
Each $v\in\mathcal D^M$ decomposes uniquely as
$v_D+P\gamma_l v$, with $v_D\in\mathcal D^D$.
Orthogonality of harmonic lifts to $\mathcal D^D$ gives

$$
 A_s(u,v)=\langle F,v_D\rangle+b(f,\gamma_l v)
         =\langle F,v_D+P\gamma_l v\rangle.
\tag{3.7}
$$

Uniqueness proves (3.1), and factorization proves (3.2). This is the
strong form-resolvent identity of Olaf Post,
[*Boundary pairs associated with quadratic forms*, arXiv:1210.4707v2](https://arxiv.org/pdf/1210.4707v2),
Theorem 4.3(ii), with spectral variable $z=-s$, boundary map $\gamma_l$,
Dirichlet operator $H^D_{\epsilon,g}$, full operator $H^M_{\epsilon,g}$
and solution map $P$. The bounded bulk-$L^2$ extension required for
that strong version has been proved in (3.3)–(3.6); the weaker
energy-dual identity alone would not justify the bounded-operator
formula. Both spectra exclude $-s$ by (1.3). The direct computation
(3.7) fixes its positive sign independently of conormal convention.
$\square$

## 4. One fixed internal seam with the parent potential

**Definition 4.1 (same-source cut).** Fix
$h\in(l,u)\setminus\{k_o\}$, and let $\Omega_-=(l,h)\times\mathbb T^2$,
$\Omega_+=(h,u)\times\mathbb T^2$ and
$\Sigma_h=\{h\}\times\mathbb T^2$. On both slabs use the restriction
of the PARENT multiplier $\Gamma_{\epsilon,o}$. In particular the
slab without $o$ has a bounded multiplier, and the slab containing
$o$ has exactly the original singular coefficient. Let $H^J$ be the
both-outer-killed attractive realization on the joined cylinder, and
$H^{\rm cut}=H^{\rm cut}_-\oplus H^{\rm cut}_+$ the realization with
an additional Dirichlet condition at $h$. A zero-noise critical slab
uses its ground-transform completion with the same $H$ near the pole.
On each slab the free outer face has zero value; only the seam trace
is allowed to vary in the comparison form.

**Theorem 4.2 (finite seam spectral reconstruction).** There is a finite
$B_h\ge B$ depending also on this fixed seam, such that for every
finite $S_h\ge B_h+1$ and
$B_h+1\le s\le S_h$, all noise/coupling pairs of Definition 1.1 admit
a positive closed common-trace seam form $b_h$, an attained lift
$P_h$, and a positive compact inverse $C_h$. Its trace domain is
exactly the free common-trace domain from C, (26.4), extended to zero
noise by the two one-face modal closures. Moreover

$$
 (H^J+s)^{-1}=(H^{\rm cut}+s)^{-1}+P_hC_hP_h^*,\qquad
 \|P_h\|\le p_{A,h}<\infty
\tag{4.1}
$$

uniformly over these ranges. If $C_h^{(\eta)}$ retains precisely the
seam eigenvalues $>\eta$, then it has finite rank and

$$
 \|(H^J+s)^{-1}-[(H^{\rm cut}+s)^{-1}
                   +P_hC_h^{(\eta)}P_h^*]\|\le p_{A,h}^2\eta.
\tag{4.2}
$$

A strict error convention retains eigenvalues $\ge\eta$ instead.
No assertion is made uniformly over seams approaching $o$, over
shrinking slabs, or over infinitely many recursive cuts.

Proof. Apply the proof of (1.6) on the pole-containing slab, choosing
$\chi$ supported away from its seam and outer face. A function
supported in that interior is an original killed test, so $B_D$ still
applies; no slab Green field is needed. On the other slab use its
uniformly bounded parent multiplier. Choose $B_h$ to dominate the
resulting two lower-bound constants and $B$. Their sum controls free
energy outside a fixed source neighbourhood plus the total bulk norm.
The local ground transform (1.8) and the collar/kernel argument of
Theorem 1.2 give exactly the two completed slab spaces and their trace
kernels. The trace of a joined member agrees from both sides. Conversely,
matching traces glue their free exterior collars in the modal horizontal
domain; the only possible completed singularity is strictly inside one
slab. A partition of unity then identifies this glued domain with the
original joined completed domain. Thus matching traces, rather than a
new abstract coupling rule, recover $H^J$.

Let $n_h^0$ denote the free summed seam energy of C, (26.4). Applying
(2.5) to the two sides and taking free competitors gives

$$
 [\max(1,S_h)]^{-1}n_h^0[f]\le b_h[f]\le n_h^0[f].
\tag{4.3}
$$

At zero noise each summand is the actual one-face minimum from C,
(31.2), after reversing height on the lower slab; the sign of the
slope may reverse and C, Theorem 32.1 explicitly allows either sign.
Finite Fourier approximation proves the common-trace domain assertion
there as well. The free seam weights tend to infinity off finite
lattice sets and are bounded below by
$(h-l)^{-1}+(u-h)^{-1}$. Therefore (4.3) gives a closed positive form
and compact inverse with finite-rank spectral truncations.

For bulk boundedness repeat (3.3)–(3.6) with the free joined seam lift.
C, Proposition 26.3 gives its free bound
$p_h=\sqrt{(u-l)/3}$; its convex-ODE proof remains valid at zero noise.
Choose $\theta=1$ near $k_o$, supported strictly inside the
pole-containing slab, and $\theta_1=1$ on its derivative support.
The same cutoff harmonic identity applies inside that slab, and its
commutator has no contribution at the seam. Formula (3.6), with $p_h$
and these cutoffs and with the supremum of the SAME parent potential
on $\operatorname{supp}(1-\theta)$, supplies a finite $p_{A,h}$.
The Riesz correction is now in the decoupled killed completed domain.
This proves the strong $L^2$ realization on the two-slab direct sum.

The orthogonal decomposition in (3.7), with seam trace and decoupled
kernel, proves (4.1). The outward flux is
$\partial_k|_{h-}-\partial_k|_{h+}$; it is the sum of outward fluxes.
Factorization and the spectral tail prove (4.2). This is a single
finite spectral correction to exact slab inverses, not a replacement
of those inverses by finite-rank operators. The Post correspondence
is the one stated after (3.7), with $(\gamma_l,H^M,H^D)$ replaced by
$(\gamma_h,H^J,H^{\rm cut})$. All potential restrictions, measures,
source normalization and spectral parameters have remained identical.
$\square$

## 5. Sharp uniform failure and the spatial-realization boundary

**Theorem 5.1 (failure of a common shifted positive minimum above $g_*$).**
Fix any $g>g_*$ and any finite real shift $s$. For arbitrarily small
positive $\epsilon$ there is a smooth punctured-core function $v_\epsilon$
with both height traces zero and

$$
 q_{\epsilon,g}[v_\epsilon]+s\|v_\epsilon\|_2^2<0.
\tag{5.1}
$$

Consequently at those noises the mixed boundary minimization with
zero prescribed lower trace has infimum $-\infty$. No single fixed
shift supplies a positive minimizing response over a noise interval
containing arbitrarily small positive noise. This excludes exactly
that uniform positive variational contract, and does not exclude
indefinite or meromorphic DtN constructions or noise-dependent shifts.

Proof. C, Theorems 16.1 and 16.3 give
$\epsilon^2E_\epsilon(g)\to e(g/m_0)<0$.
Hence $E_\epsilon(g)+s<0$ for all sufficiently small positive noise.
The free killed form core, punctured at the point by the capacity
argument in C, Theorem 16.3, approximates its Rayleigh infimum at each
fixed positive noise. Choose a normalized core member satisfying
(5.1). It is also a mixed competitor with zero lower trace. Multiplying
it by arbitrarily large real constants preserves that trace and drives
its shifted energy to $-\infty$. Adding such a zero-trace direction
to any fixed competitor with another prescribed trace likewise gives
a negative quadratic leading term. This proves the failure assertion
without assuming anything about an indefinite spectral definition.
$\square$

**Definition 5.2 (observations and remaining realization problem).** The
boundary input is an arbitrary raw complex $L^2$ conormal forcing;
the observed output is its raw lower $L^2$ trace. The source, operator,
measure and covariance-$2$ clock are those of Definition 1.1. The
closed positive response, its completed zero-noise endpoint, the
bounded Poisson realization, the same-potential mixed comparison and
one fixed internal-seam reconstruction constitute the native composition
in Theorems 1.2–4.2. Their general IMS, KLMN, trace-form, min–max,
spectral truncation and resolvent ingredients are literature-attested;
the exact source/critical-domain correspondence and uniform attractive
transfer proved here are repository-derived. No global literature
priority claim is made.

The orders $\eta^{-3}$ at zero noise and
$\epsilon^{-1}\eta^{-2}$ below positive noise quantify this entire
operator family. A fixed pole datum is one member, and the family rank
lower bound is not a lower bound for that datum. These ranks are not
bit counts or counts of Euclidean spatial axes. There remains a
separate common-source physical-realization problem: identify lawful
native preparations, observations and operations that realize this
forcing family and its spectral consumers, with their joint law,
original clock, resource accounting and three spatial observables.
The analytic attractive form does not supply that correspondence.
Neither finite gluing nor attraction alone proves uniform infinite
refinement or selects a universal physical spatial dimension.

## 追加锚（本行以下为增补区）
