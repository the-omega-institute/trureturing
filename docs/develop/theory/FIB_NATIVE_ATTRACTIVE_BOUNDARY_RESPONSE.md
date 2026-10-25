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
Theorem 4.3(ii). To meet its nonnegative-form convention, use
$h=q^M_{\epsilon,g}+B\|\cdot\|_2^2$, spectral variable $z=B-s$,
boundary map $\gamma_l$, Dirichlet operator $H^D_{\epsilon,g}+B$,
full operator $H^M_{\epsilon,g}+B$ and solution map $P$. At its
reference point $z=-1$ this is exactly $s=s_0$. The bounded bulk-$L^2$ extension required for
that strong version has been proved in (3.3)–(3.6); the weaker
energy-dual identity alone would not justify the bounded-operator
formula. Both unshifted spectra exclude $-s$ by (1.3), so both shifted spectra
exclude $z=B-s$. The direct computation
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
$(\gamma_h,H^J,H^{\rm cut})$, using the nonnegative shift $B_h$
and spectral variable $z=B_h-s$. All potential restrictions, measures,
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

## 6. Coupling derivatives for a moving original pole

**Definition 6.1 (native parameters and five response coefficients).**
In §§6–8 fix $0<Z<1$, $r=1-Z$, $0<l<u<r/2$, $h=u-l$ and
$\sigma>0$. Retain the preparation rotations, the two actual $2\pi$
periods, raw measures, vector fields and covariance-$2$ clock of
Definition 1.1. The suppliers C and V in these sections, and the
quotient supplier
[F](FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md), are their texts at
revision `48709befec1fa9346ef6ef7d4c62091f7d849e26`.
Let

$$
\begin{aligned}
p&=(y,\alpha_o,\beta_o,a,v)
 \in(0,h)\times\mathbb T^2\times(0,\infty)\times[0,\infty),\\
o&=(l+y,\alpha_o,\beta_o),\qquad \epsilon=\sqrt v,\qquad g=\kappa a.
\end{aligned}
\tag{6.1}
$$

Here $a$ is an attractive gain and $\kappa\ge0$ a known coupling
multiplier. The field $\Gamma_{\sqrt v,o}$ remains the complete
both-face killed FREE unit-source Green field; $a$ does not change its
source normalization. On the free mixed domain $\mathcal V_{\sqrt v}$
of C, (31.1), write

$$
\begin{aligned}
t_{v,s}(w,z)&=T_{\sqrt v}(w,z)+s\langle w,z\rangle,\\
W_p(w,z)&=a\int_\Omega\Gamma_{\sqrt v,o}w\overline z\,d\mu,\\
b_{p,\kappa,s}[f]
 &=\min_{\substack{w\in\mathcal V_{\sqrt v}\\\gamma_lw=f}}
           \{t_{v,s}[w]-\kappa W_p[w]\}.
\end{aligned}
\tag{6.2}
$$

Only sufficiently small $\kappa$ is used. The trace domain is the
free trace-energy domain $\mathcal T_{\sqrt v,s}$, and the upper trace
is zero. Polarization is linear in its first argument. Put
$e_d=(2\pi)^{-1}\exp(i(d_1\alpha+d_2\beta))$, $e_0=e_{(0,0)}$, and

$$
\begin{aligned}
B_d(s)&=-\left.\partial_\kappa b_{p,\kappa,s}(e_d,e_0)
                                                    \right|_{0+},\\
c(v)&=\lambda_{0,1}^{\sqrt v}(0),\\
\Phi(p)&=(c(v),B_0(0),B_0(\sigma),B_{(1,0)}(0),B_{(0,1)}(0))
                       \in\mathbb R^3\times\mathbb C^2.
\end{aligned}
\tag{6.3}
$$

For modal formulas set $x=k-l$ and, for $d\in\mathbb Z^2$, define

$$
\begin{aligned}
q_d(x)&=d_1/2+(1/2-(l+x)/r)d_2,\\
H_d^v&=-\partial_x^2+q_d(x)^2+vd_2^2/r^2,\\
G_d^v(x,y)&=(H_d^v)^{-1}(x,y)\quad\hbox{with two Dirichlet endpoints},\\
(H_d^v+s)\psi_{d,s}^v&=0,\qquad
       \psi_{d,s}^v(0)=1,\quad\psi_{d,s}^v(h)=0,\\
F_{d,s}(y,v)&=\int_0^hG_d^v(x,y)\psi_{d,s}^v(x)\psi_{0,s}(x)\,dx,\\
H_s(y)&=F_{0,s}(y,v),\qquad
\psi_{0,s}(x)=
\begin{cases}
\sinh(\sqrt s(h-x))/\sinh(\sqrt s h),&s>0,\\
1-x/h,&s=0.
\end{cases}
\end{aligned}
\tag{6.4}
$$

Write $\lambda_d^{\sqrt v}(s)=-(\psi_{d,s}^v)'(0)$ for the free
one-face energy of C, (31.2). The Green kernel in $F_{d,s}$ is
unshifted; only the two Poisson profiles use $s$. Thus $H_s$ is
independent of $v$. These are the
original modes of C, Definitions 31.1–31.2 and Theorem 34.1, without
an altered clock or a regenerated mixed Green potential.

**Theorem 6.2 (uniform small-coupling derivative and its raw phase).**
Fix $0<\delta<h/2$, $0<a_{\min}\le a_{\max}<\infty$ and
$0\le v_{\max}<\infty$, and put

$$
K=[\delta,h-\delta]\times\mathbb T^2
                   \times[a_{\min},a_{\max}]\times[0,v_{\max}].
\tag{6.5}
$$

There is $M<\infty$ such that, for all $p\in K$, $s\ge0$ and
$w\in\mathcal V_{\sqrt v}$,

$$
0\le W_p[w]\le M T_{\sqrt v}[w]\le M t_{v,s}[w].
\tag{6.6}
$$

Consequently for $0\le\kappa\le\kappa_0$, with some common
$\kappa_0>0$, the minimum (6.2) is coercive and uniquely attained,
on exactly that free mixed domain, also for $s=0$ and $v=0$.
For every fixed $d$ and $s\ge0$ its derivative exists and is

$$
B_d(s)=\frac{a}{4\pi^2}
       e^{i(d_1\alpha_o+d_2\beta_o)}F_{d,s}(y,v).
\tag{6.7}
$$

In particular $B_0(s)=aH_s(y)/(4\pi^2)>0$, and both selected
nonzero-mode coefficients are nonzero. For each fixed parameter $p$
these conclusions hold on a neighbourhood of $\kappa=0$ without a
compact-parameter restriction.

Proof. First verify the uniform mixed-domain bound, rather than
deducing it from a positive shift or from positive-noise ellipticity.
Use the exact source chart C, (15.1), with raw Jacobian
$m_0=(2r)^{-1}$. The local remainder C, (3.2), and exterior bound
C, (15.4), can be chosen uniformly for the poles in (6.5) and
$0\le\epsilon\le\sqrt{v_{\max}}$. To see the uniformity in the pole,
choose the chart height radius below $\delta/4$. In C, Theorem 3.1's
proof, wall errors then have one positive height separation; nontrivial
deck images in C, (2.3), have one positive separation because their
horizontal displacement is $4\pi n$, and for $n=0$ their central
displacement is $2\pi r m$. The remaining shear $c(k_o)$ ranges over
a compact interval. Thus the polynomial image counts and the integrable
$Ct^{-2}e^{-b/t}$ errors have common constants. Off a smaller chart
the minimum image distance is bounded below, so the same small-time
Gaussian upper bound is integrable there. The positive-time tail in
C, Theorem 1.3 is uniform in both kernel variables. These are exactly
the bounds used to prove (3.2) and (15.4), so the same constants
work on this compact pole set, including the zero-noise limit. If
$v_{\max}=0$, choose any auxiliary positive upper noise bound.
Torus translations remove dependence on $\alpha_o,\beta_o$.

Here is the needed local form control. By C, Definition 16.2,
$\int\mathcal G_1|u|^2\le\Lambda_*^{-1}\mathcal T_1[u]$.
The exact dilation C, (16.6), gives, for every $\epsilon>0$,

$$
\int\mathcal G_\epsilon|u|^2\,d\xi
 \le\Lambda_*^{-1}\mathcal T_\epsilon[u].
\tag{6.8}
$$

At $\epsilon=0$ this same inequality follows from
$\mathcal G_0=(2\pi)^{-1}R^{-2}$ and C, (16.11)–(16.12), since
$\Lambda_*\le2\pi\lambda_0$. These existing inequalities extend
from compact smooth tests to their form closures. For the zero-noise
punctured core one can remove the puncture: a cutoff at radius $t$
has horizontal energy $O(t^2)$ against a bounded smooth function,
because the homogeneous dimension is four. Thus it imposes no point
condition on a smooth test or on the horizontal closure.

Choose real smooth cutoffs $\chi_o,\zeta_o$ with
$\chi_o^2+\zeta_o^2=1$, $\chi_o=1$ on a smaller source chart,
$\operatorname{supp}\chi_o$ compact in the original chart, and
$\zeta_o=0$ near $o$. Their three field derivatives have common bounds
over this compact family. Pulling $\chi_ow$ to the group, (6.8) and
the raw Jacobian show

$$
\int\Gamma_{\sqrt v,o}|\chi_ow|^2d\mu
 \le g_*^{-1}T_{\sqrt v}[\chi_ow]+B\|\chi_ow\|_2^2,
 \qquad g_*=m_0\Lambda_*>0.
\tag{6.9}
$$

The exterior part is at most $B'\|\zeta_ow\|_2^2$. The product rule
and uniform cutoff bounds therefore give
$\int\Gamma_{\sqrt v,o}|w|^2\le C(T_{\sqrt v}[w]+\|w\|_2^2)$
on the mixed smooth core. No lower trace condition was used: only
$\chi_ow$ has to be an interior test. C, (31.1)'s height inequality
$\|w\|_2^2\le h^2T_{\sqrt v}[w]/2$ absorbs the norm term.
Multiplication by $a\le a_{\max}$ proves (6.6). For a free mixed
approximating sequence, (6.6) makes it Cauchy in the potential-weighted
$L^2$ norm. An almost-everywhere convergent subsequence identifies that
weighted limit with the original function, since the Green field is
finite off its measure-zero pole. Hence the integral and bound extend
to the entire mixed domain, including its horizontal closure at zero.
This proves (6.6) without assuming $g_*=g_{\mathrm c}$.

Take $M>0$ larger if necessary and
$\kappa_0\le\min\{(2M)^{-1},g_*/(2a_{\max})\}$.
The form $t_{v,s}-\kappa W_p$ lies between
$(1-\kappa M)t_{v,s}$ and $t_{v,s}$. Since $t_{v,s}$ is a Hilbert
norm on the free mixed domain, and its trace kernel is the free
both-zero-trace domain $\mathcal F_{\sqrt v}$, orthogonal projection
onto each affine trace class proves the minimum assertion and leaves
the trace domain unchanged. This is a subcritical unshifted assertion;
it invokes no completed critical-coupling domain.

For completeness, the derivative follows by a bounded form calculation.
Let $w_f^0=\mathcal P_{\sqrt v,s}f$ be the free lift and write the
attractive lift as $w_f^\kappa=w_f^0+z_f^\kappa$, where
$z_f^\kappa\in\mathcal F_{\sqrt v}$. Free orthogonality gives

$$
\begin{aligned}
(t_{v,s}-\kappa W_p)(z_f^\kappa,q)
 &=\kappa W_p(w_f^0,q)\quad(q\in\mathcal F_{\sqrt v}),\\
\|z_f^\kappa\|_{t_{v,s}}
 &\le\frac{\kappa M}{1-\kappa M}\|w_f^0\|_{t_{v,s}},\\
\frac{b_{p,0,s}(f,z)-b_{p,\kappa,s}(f,z)}{\kappa}
 &=W_p(w_f^\kappa,w_z^0).
\end{aligned}
\tag{6.10}
$$

The last equality uses attractive orthogonality to replace the second
attractive lift by $w_z^0$, and then free orthogonality to remove
$z_f^\kappa$ from the free term. Potential Cauchy–Schwarz and (6.6)
justify all pairings. Letting $\kappa\downarrow0$ yields
$B_d(s)=W_p(\psi_{d,s}^ve_d,\psi_{0,s}e_0)$.
This is the classical product-of-solutions linearization of a boundary
form, with its singular-potential and mixed-domain justification supplied
by (6.6)–(6.10). Compare the bounded-potential harmonic-products problem
in Dos Santos Ferreira–Kurylev–Lassas–Liimatainen–Salo,
[*The linearized Calderón problem in transversally anisotropic geometries*,
arXiv:1712.04716v1](https://arxiv.org/html/1712.04716v1), Question 1.1
and Theorem 1.1; its Riemannian hypotheses are not imposed here.
The trace-form construction itself is the classical boundary-pair method
in Post, [arXiv:1210.4707v2](https://arxiv.org/html/1210.4707v2), §§2.2–2.5.

Finally the original Green expansion of C, Theorem 34.1 has modes
$G_j^v(x,y)e_j(\theta)\overline{e_j(\theta_o)}$.
The product of the two free lifts is
$(4\pi^2)^{-1}\psi_{d,s}^v\psi_{0,s}\exp(id\cdot\theta)$.
Its torus integral against the Green field selects $j=-d$.
Since $H_{-d}^v=H_d^v$, the result is exactly (6.7), with positive
phase sign and raw factor $(4\pi^2)^{-1}$. This pairing may be taken
distributionally against the smooth finite-mode product; equivalently
it follows by integrating its Fourier coefficient. The Green field is
integrable by C, (1.6), so this step needs no pointwise sum at the pole.
Positive Dirichlet Green kernels and positive interior Poisson profiles
give $F_{d,s}>0$. Each fixed $p$ belongs to a compact set of the form
(6.5), which proves the final assertion. $\square$

## 7. A stable five-coefficient inverse with its native consumer

**Theorem 7.1 (joint recovery of the original pole, gain and variance).**
The map $\Phi$ of (6.3) is injective on its full parameter domain.
For every compact set $K$ in (6.5), there are constants
$0<C_1\le C_2<\infty$ such that

$$
\begin{aligned}
C_1d_K(p,p')&\le\|\Phi(p)-\Phi(p')\|\le C_2d_K(p,p'),\\
d_K(p,p')&=|y-y'|+|a-a'|+|v-v'|
 +d_{\mathbb T}(\alpha_o,\alpha'_o)
 +d_{\mathbb T}(\beta_o,\beta'_o),
\end{aligned}
\tag{7.1}
$$

where the data norm is Euclidean on $\mathbb R^3\times\mathbb C^2$
and each circle distance is the shortest arc length. In particular the
variance endpoint $v=0$ is included. The recovered point is the
original native point $o$, so, after removing the fixed preparation
rotations, it determines the supplied coherences

$$
z_o=\sqrt{k_o(r/2-k_o)}e^{i\alpha_o},\qquad
w_o=\sqrt{Zk_o}e^{i\beta_o},\qquad k_o=l+y.
\tag{7.2}
$$

For a specified original finite command with total increments $(A,B)$,
chronological integral $J$, and prefix height extrema $(m,M)$, it also
determines its cylinder guard and, when that guard holds, its endpoint:

$$
\begin{aligned}
&l<k_o+m,\qquad k_o+M<u,\\
&\left(k_o+A,\ [\alpha_o+B/2],\
 [\beta_o+(1/2-k_o/r)B-J/r]\right).
\end{aligned}
\tag{7.3}
$$

This is recovery from the supplied analytic boundary coefficients, with
no additional command, re-preparation or acquisition right.

Proof. All scalar ODEs in (6.4) have nonnegative smooth potentials.
Their two-endpoint homogeneous Dirichlet operators are strictly
positive. Their Green kernels and their Poisson profiles are positive
in the interval. For the finitely many modes used here, ordinary
parameter-dependent ODE theory gives smooth dependence on $v$ down to
zero: the coefficients are affine in $v$, and the invertible Dirichlet
problem persists in a small open parameter neighbourhood of each
$v\ge0$. This statement concerns individual one-dimensional problems,
not an identification of the full positive-noise and zero-noise bulk
domains. It also shows that $F_{d,s}$ is smooth in $(y,v)$, since

$$
H_d^v F_{d,s}(\cdot,v)=\psi_{d,s}^v\psi_{0,s},\qquad
F_{d,s}(0,v)=F_{d,s}(h,v)=0.
\tag{7.4}
$$

First recover $v$. Differentiating the one-face minimum for $d=(0,1)$
and using its stationary equation, whose variation has zero endpoint
values, gives

$$
c'(v)=r^{-2}\int_0^h(\psi_{(0,1),0}^v(x))^2dx>0.
\tag{7.5}
$$

This is the usual variational derivative of a simple scalar boundary
problem. Positivity and continuous parameter dependence make
$\min_{[0,v_{\max}]}c'(v)>0$ and $\max c'(v)<\infty$.
When $v_{\max}=0$ only the single variance value is in $K$.
Thus $c$ is globally strictly increasing and has a Lipschitz inverse
on every such compact interval, with a right derivative at zero.

Next put $R(y)=H_\sigma(y)/H_0(y)$. In the original zero mode,

$$
\begin{aligned}
G_0(x,y)&=\frac{\min(x,y)(h-\max(x,y))}{h},\\
H_s(y)&=\int_0^hG_0(x,y)\psi_{0,s}(x)^2dx,\\
H_0(y)&=hy/4-y^2/2+y^3/(3h)-y^4/(12h^2)>0.
\end{aligned}
\tag{7.6}
$$

The polynomial follows by solving $-H_0''=(1-y/h)^2$ with two zero
endpoints. To establish strictness of the inverse height dependence,
define, for $0<x<h$,

$$
f(x)=\psi_{0,0}(x)^2,\qquad
q(x)=\frac{\psi_{0,\sigma}(x)^2}{\psi_{0,0}(x)^2},\qquad
d\mu_y(x)=\frac{G_0(x,y)f(x)}{H_0(y)}dx.
\tag{7.7}
$$

Then $\mu_y$ is a probability measure and $R(y)=\int q\,d\mu_y$.
The ratio before squaring in $q$ is
$h\sinh(t(h-x))/((h-x)\sinh(th))$, $t=\sqrt\sigma>0$.
It is strictly decreasing in $x$, because
$z\cosh z-\sinh z>0$ for $z>0$, as follows by differentiating this
last expression and using its value zero at zero. Hence $q$ is
strictly decreasing. The likelihood score of the Green kernel is

$$
\partial_y\log G_0(x,y)=
\begin{cases}
-(h-y)^{-1},&x<y,\\
y^{-1},&x>y.
\end{cases}
\tag{7.8}
$$

Let $L_y=\mu_y((0,y))$, $U_y=\mu_y((y,h))$, and let
$q_L(y),q_U(y)$ be the corresponding conditional means of $q$.
Both masses are positive, sum to one, and $q_L(y)>q_U(y)$.
Differentiating the normalized integral in (7.7) gives the exact
covariance identity

$$
R'(y)=\frac{hL_yU_y}{y(h-y)}(q_U(y)-q_L(y))<0.
\tag{7.9}
$$

The two integrals split at $x=y$ have matching integrands there, so
the differentiation introduces no unaccounted boundary term. All
functions in (7.9) are continuous for $0<y<h$. Consequently
$\rho_K=\min_{[\delta,h-\delta]}(-R')>0$.
This is the elementary monotone-likelihood/covariance argument applied
to this specific unshifted Green weight, not an inference from
non-strict positivity or merely from injectivity.

Equations (6.7) now give the exact inverse in a triangular order:

$$
\begin{aligned}
v&=c^{-1}(\Phi_1),&
y&=R^{-1}(B_0(\sigma)/B_0(0)),&
a&=4\pi^2B_0(0)/H_0(y),\\
e^{i\alpha_o}&=B_{(1,0)}(0)/|B_{(1,0)}(0)|,&
e^{i\beta_o}&=B_{(0,1)}(0)/|B_{(0,1)}(0)|.
\end{aligned}
\tag{7.10}
$$

The inverses are only evaluated on the actual data image. Their
denominators are positive; the phase amplitudes are positive by
Theorem 6.2. These formulas prove global injectivity on the actual
torus, rather than recovery modulo an extra phase quotient.

Here are quantitative bounds for the inverse on $K$. Write
$D=B_0(0)$ and $N=B_0(\sigma)$. There is $b_K>0$ with
$D\ge b_K$, since $a\ge a_{\min}$ and $H_0$ is positive on the
compact height interval. Also $0<N/D\le1$ because
$0<\psi_{0,\sigma}\le\psi_{0,0}$ in the interior. For two image
points,

$$
\left|\frac ND-\frac{N'}{D'}\right|
 \le\frac{|N-N'|+|D-D'|}{b_K},\qquad
|y-y'|\le\frac{|N-N'|+|D-D'|}{b_K\rho_K}.
\tag{7.11}
$$

The lower derivative bound in (7.5) controls $|v-v'|$ by
$|c(v)-c(v')|$. Put $H_{\min}=\min H_0>0$ and
$L_H=\max|H_0'|$ on the compact height interval. Then

$$
|a-a'|\le\frac{4\pi^2}{H_{\min}}|D-D'|
             +\frac{a_{\max}L_H}{H_{\min}}|y-y'|.
\tag{7.12}
$$

For each selected nonzero mode, (6.7), positivity and compactness give
a common lower bound $m_K>0$ for its modulus. For complex numbers
$z,z'$ of modulus at least $m_K$,

$$
\left|\frac z{|z|}-\frac{z'}{|z'|}\right|
 \le\frac{2|z-z'|}{m_K},\qquad
d_{\mathbb T}(\arg z,\arg z')
 \le\frac\pi2\left|\frac z{|z|}-\frac{z'}{|z'|}\right|.
\tag{7.13}
$$

The second inequality is the shortest-arc versus chord inequality on
the full circle, so it does not introduce a branch-cut discontinuity.
Summing (7.11)–(7.13) and the variance bound, and comparing the finite
coordinate norm with the Euclidean data norm, proves the lower bound
in (7.1). Smoothness of $c,H_s,F_{d,s}$ on the compact parameter
rectangle and $|e^{it}-e^{it'}|\le d_{\mathbb T}(t,t')$ prove the
upper bound. Thus the lower bound does not rely on a bare compact
injectivity argument.

Finally F, (1.2)–(1.4), identifies (7.2) with the original bottom
and middle-reference coherences. The original finite chronology,
used in V, (29.2), and in
[Guarded lift limits](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md),
Proposition 2.3, gives (7.3) at every prefix; imposing the two cylinder
walls yields exactly its displayed guard. This is a consumer of the
recovered native $o$, not a new chronological law. Exact guards may
be evaluated from exact parameters. A noisy parameter estimate alone
does not certify a guard with no promised distance from refusal.

Finite-measurement uniqueness and Lipschitz stability are classical
inverse-problem goals. Alberti–Santacesaria,
[*Calderón's inverse problem with a finite number of measurements*,
Forum of Mathematics, Sigma 7](https://doi.org/10.1017/fms.2019.31),
Theorems 1–2, treat bounded potentials in a known finite-dimensional
linear subspace for a Euclidean Schrödinger problem, with full boundary
outputs for finitely many Dirichlet inputs. That result does not
apply directly to this moving singular Green multiplier or to the
zero-noise horizontal operator. Likewise,
[*Recovering point sources for the inhomogeneous Helmholtz equation*,
arXiv:2104.14991v3](https://arxiv.org/html/2104.14991v3), Theorem 1.1,
concerns point masses on the right-hand side, radiating solutions and
boundary Cauchy data. The new composition here is (6.7)–(7.10) for
the original native attractive boundary family, including the compact
quantitative inverse (7.1). C, Theorem 34.1's supplied free exit
density is a different interface and is not substituted for these
attractive-response coefficients. No global literature-priority
assertion is part of this theorem. $\square$

## 8. Finite coupling, coefficient error and the acquisition boundary

**Theorem 8.1 (attained compact decoding from supplied secants).**
For every $K$ in (6.5) there are $\kappa_0>0$ and $C<\infty$ such
that, for all $p\in K$, $0<\kappa\le\kappa_0$ and the four pairs

$$
\mathcal I=\{((0,0),0),((0,0),\sigma),((1,0),0),((0,1),0)\},
\tag{8.1}
$$

the supplied secant coefficients satisfy

$$
D_{d,\kappa}(s):=
 \frac{b_{p,0,s}(e_d,e_0)-b_{p,\kappa,s}(e_d,e_0)}{\kappa},
\qquad |D_{d,\kappa}(s)-B_d(s)|\le C\kappa.
\tag{8.2}
$$

Suppose that each supplied value of $c(v)$ and each boundary form
coefficient in these quotients has absolute error at most $\eta\ge0$.
Let $\widetilde\Phi_\kappa$ consist of that supplied free coefficient
and the four supplied quotients, taking real parts in the three real
data coordinates. Then

$$
\|\widetilde\Phi_\kappa-\Phi(p)\|
 \le C(\kappa+\eta/\kappa+\eta).
\tag{8.3}
$$

There is a nearest-image decoder $\widehat p\in K$ minimizing
$\|\Phi(q)-\widetilde\Phi_\kappa\|$ over $q\in K$. Every such
minimizer satisfies

$$
d_K(\widehat p,p)\le C(\kappa+\eta/\kappa+\eta).
\tag{8.4}
$$

These are conditional bounds for finitely many supplied coefficients;
existence of the minimizer does not assert an executable native
acquisition or an optimal resource bound.

Proof. Use the same $M,\kappa_0$ as in Theorem 6.2. Equation (6.10)
and potential Cauchy–Schwarz give, with $f=e_d$, $z=e_0$,

$$
\begin{aligned}
|D_{d,\kappa}(s)-B_d(s)|
 &\le M\|z_{e_d}^\kappa\|_{t_{v,s}}
                          \|w_{e_0}^0\|_{t_{v,s}}\\
 &\le\frac{\kappa M^2}{1-\kappa M}
       \sqrt{\lambda_d^{\sqrt v}(s)\lambda_{(0,0)}^{\sqrt v}(s)}.
\end{aligned}
\tag{8.5}
$$

The finitely many free one-dimensional modal energies on the right
are bounded on $0\le v\le v_{\max}$, $s\in\{0,\sigma\}$, by
their ODE continuity or by inserting the linear profile as competitor.
Also $1-\kappa M\ge1/2$. This proves (8.2), uniformly including
$v=0$, without differentiating a singular Green field in $v$ or in
its pole.

An error $\eta$ in each of the two coefficients forming a secant
produces error at most $2\eta/\kappa$ in that secant. The separate
free coefficient has error at most $\eta$. Combining this with four
applications of (8.2) in the finite Euclidean norm proves (8.3);
taking real parts cannot increase these errors. By Theorem 7.1,
$\Phi(K)$ is compact. The continuous distance to supplied data attains
its minimum there, and injectivity identifies each image minimizer
with one parameter. Since $p$ is an admissible competitor,

$$
\|\Phi(\widehat p)-\Phi(p)\|
 \le\|\Phi(\widehat p)-\widetilde\Phi_\kappa\|
          +\|\widetilde\Phi_\kappa-\Phi(p)\|
 \le2\|\widetilde\Phi_\kappa-\Phi(p)\|.
\tag{8.6}
$$

The lower inequality in (7.1) proves (8.4). The asserted attainment is
the attainment of this conditional compact minimization, not a claim
that exact coupling derivatives are finitely acquired reads. $\square$

**Definition 8.2 (scope of the inverse and its undischarged realization).**
The data in Theorems 7.1–8.1 are entries of the original analytic
attractive boundary family, supplied with their declared phases,
normalizations, coupling multiplier and error tolerance. At
$\kappa=0$ alone that boundary family is independent of $o,a$;
the derivatives or nonzero-coupling secants are essential additional
data. The compact constants require an interior pole promise, positive
gain bounded away from zero, and bounded variance. No uniform inverse
as a pole approaches a wall or as $a\downarrow0$ is specified.
The recovered noise parameter is $v=\epsilon^2$; the inverse square
root is not Lipschitz at zero. No unshifted critical-coupling response
or equality $g_*=g_{\mathrm c}$ is required.

A native sensing realization would additionally have to supply the
specified boundary inputs, outputs and coupling changes for the same
unknown source, with one joint law and clock and a finite error and
resource contract. None is an operation granted by (6.2), by an
ordinary command, or by the sampling capabilities of V, Definition
29.1. A physical spatial interpretation would additionally have to
identify lawful spatial observables and their transport and metric
relations. Theorems 6.2–8.1 identify the same-source analytic family
with its own native point and its existing guarded consumers; they
do not discharge either additional realization premise or select a
universal physical spatial dimension.

## 追加锚（本行以下为增补区）
## 9. The exact full-Green threshold and its attractive response

**Definition 9.1 (whole-group free forms and the natural angular constant).**
Use C, Definitions 15.1 and 16.2, and V, Definition 10.1 and
Theorem 10.2. Write the central coordinate of C, (15.1), as $z$
(the coordinate denoted $\theta$ there), and write $\vartheta$ for
the horizontal polar angle. Thus, on the whole group,

$$
\begin{aligned}
\xi&=(x,y,z),&d\xi&=dx\,dy\,dz,\\
U&=\partial_x-\tfrac y2\partial_z,&
V&=\partial_y+\tfrac x2\partial_z,&Z_H&=\partial_z,\\
\rho&=(x^2+y^2)^{1/2},&
R&=(\rho^4+16z^2)^{1/4},\\
\mathcal E_H[f]&=\|Uf\|_2^2+\|Vf\|_2^2,&
\mathcal T_\epsilon[f]&=\mathcal E_H[f]+\epsilon^2\|Z_Hf\|_2^2.
\end{aligned}
\tag{9.1}
$$

For $\epsilon=0,1$, let $\mathcal H_\epsilon$ be the closure of
complex $C_c^\infty(\mathbb R^3)$ in
$(\|f\|_2^2+\mathcal T_\epsilon[f])^{1/2}$. At $\epsilon=0$
only the horizontal derivatives occur. Its associated free operator
is $\mathcal L_\epsilon=-(U^2+V^2+\epsilon^2 Z_H^2)$.
Let $h_\epsilon(t,\xi)$ be its Lebesgue unit-source heat kernel,
with the original clock $e^{-t\mathcal L_\epsilon}$, and put

$$
\mathcal G_\epsilon(\xi)=\int_0^\infty h_\epsilon(t,\xi)\,dt,
\qquad \mathcal G_0(\xi)=\frac1{2\pi}R^{-2}.
\tag{9.2}
$$

The second identity is the horizontal normalization supplied by V,
Theorem 10.2; the density factor $m_0$ is absent from the whole-group
Lebesgue kernel. Define, on the complex domain,

$$
\begin{aligned}
J&=(-\pi/2,\pi/2),\qquad c(a)=\cos a,\\
\mathcal H_c&=\{b\in L^2(J;\mathbb C):
 b\in AC_{\mathrm{loc}}(J),\ \sqrt c\,b'\in L^2(J)\},\\
\lambda_0&=\inf_{0\ne b\in\mathcal H_c}
 \frac{\int_J(4c|b'|^2+c|b|^2)\,da}{\int_J|b|^2\,da},
 \qquad K=2\pi\lambda_0>0.
\end{aligned}
\tag{9.3}
$$

These are natural finite-energy endpoints, with no imposed Dirichlet
values. Splitting real and imaginary parts leaves the infimum
unchanged. The whole-group free forms $\mathcal T_\epsilon$ and
$\mathcal H_\epsilon$ are distinct from the slab forms $T_\epsilon$,
$q^M_{\epsilon,g}$ and $q^D_{\epsilon,g}$ in Definition 1.1.
The latter use $d\mu$, the original killed field
$\Gamma_{\epsilon,o}$ and their stated wall traces; neither those
traces nor the factor $m_0=(2r)^{-1}$ are inserted into (9.1)–(9.3).
The partial Fourier convention throughout this section is

$$
\widehat f(X,k)=\int_{\mathbb R}e^{-ikz}f(X,z)\,dz,
\qquad f(X,z)=\frac1{2\pi}\int_{\mathbb R}e^{ikz}\widehat f(X,k)\,dk,
\qquad X=(x,y).
\tag{9.4}
$$

**Theorem 9.2 (the exact full-Green inequality on the original free domain).**
For every complex $u\in\mathcal H_1$, including $u=0$,

$$
\mathcal T_1[u]\ \ge\ 2\pi\lambda_0
       \int_{\mathbb R^3}\mathcal G_1(\xi)|u(\xi)|^2\,d\xi.
\tag{9.5}
$$

The weight is the complete heat integral (9.2). The assertion includes
all angular modes and imposes no symmetry on $u$.

Proof. First extend the precise horizontal input of V, Theorem 10.2,
to the domain needed below:

$$
\mathcal E_H[f]\ge\lambda_0\int R^{-2}|f|^2\,d\xi
       =K\int\mathcal G_0|f|^2\,d\xi,
       \qquad f\in\mathcal H_1.
\tag{9.6}
$$

The supplied theorem applies to every complex smooth punctured test.
For a compact smooth test $f$, choose a cutoff zero on the Euclidean
ball of radius $\delta$, one outside the ball of radius $2\delta$,
with derivatives $O(\delta^{-1})$. On the fixed compact support all
three frame coefficients are bounded. The additional squared-derivative
cost is $O(\delta^3\delta^{-2})=O(\delta)$; the removed original
norms and derivative integrals tend to zero. Thus the punctured tests
converge in the $\mathcal H_1$ norm. Fatou proves (9.6) on the full
smooth compact core. A defining core approximation to any
$f\in\mathcal H_1$, followed by an almost-everywhere convergent
subsequence and Fatou again, proves (9.6) as stated. In particular its
weighted integral is finite. This uses the supplied horizontal theorem,
not an identification of $\mathcal H_1$ with Euclidean $H^1$.

Next compute the exact central Fourier heat columns. For $t>0$,
$k\ne0$ and $\kappa=|k|$, they are

$$
\begin{aligned}
q_\epsilon(t,\rho,k)
 &:=\int_{\mathbb R}e^{-ikz}h_\epsilon(t,\rho,z)\,dz\\
 &=e^{-\epsilon^2tk^2}
   \frac{\kappa}{4\pi\sinh(\kappa t)}
   \exp\!\left(-\frac{\kappa\rho^2}{4}\coth(\kappa t)\right),\\
q_\epsilon(t,\rho,0)
 &=\frac1{4\pi t}\exp\!\left(-\frac{\rho^2}{4t}\right),
 \qquad 0\le q_1(t,\rho,k)\le q_0(t,\rho,k).
\end{aligned}
\tag{9.7}
$$

Here the value at zero is the continuous limit, not an omitted mode.
To justify both the formula and its operator domain, Plancherel in
(9.4) transforms the free form into the direct integral, with measure
$dk/(2\pi)$, of the closed magnetic forms

$$
\| (\partial_x-iky/2)F\|_{L^2_X}^2
 +\| (\partial_y+ikx/2)F\|_{L^2_X}^2
 +\epsilon^2k^2\|F\|_{L^2_X}^2.
\tag{9.8}
$$

This identity first holds on smooth tests. For the closure, truncate
$k$ and $X$, using horizontal cutoffs whose product-rule errors tend
to zero. On the resulting bounded sets the coefficients are bounded,
so smoothing gives compact smooth approximants in $(X,k)$ in the
direct-integral form norm. Their inverse transforms are smooth,
compactly supported in $X$ and rapidly decreasing in $z$. Cut them
off at $|z|\le 2N$ by cutoffs equal to one for $|z|\le N$.
The extra $U,V$ derivatives are $-(y/2)\chi_N' f$ and
$(x/2)\chi_N'f$; their norms tend to zero because the horizontal
support is bounded and $\|\chi_N'\|_\infty=O(N^{-1})$.
The central derivative error, when present, has the same bound.
The original derivatives converge by their integrable tails.
This gives the original compact smooth core, and identifies (9.8)
with its original Friedrichs closure, for both $\epsilon=0$ and $1$.

The fiber operator is $B_k+\epsilon^2k^2$, where

$$
B_k=-\Delta_X-ik\partial_\vartheta+k^2\rho^2/4.
\tag{9.9}
$$

It commutes with horizontal rotations. On the radial reducing
subspace its closed form is exactly that of
$H_\kappa=-\Delta_X+\kappa^2|X|^2/4$; only on that subspace does
the angular term vanish. The source $\delta_{X=0}$ is radial.
Applying the fiber semigroup to radial smooth approximate identities
therefore computes its source column from $H_\kappa$, with the
additional scalar $e^{-\epsilon^2tk^2}$.

The classical two-dimensional oscillator Mehler formula is

$$
M_\kappa(t;X,Y)=\frac{\kappa}{4\pi\sinh(\kappa t)}
 \exp\!\left[-\frac{\kappa}{4\sinh(\kappa t)}
 \{\cosh(\kappa t)(|X|^2+|Y|^2)-2X\cdot Y\}\right].
\tag{9.10}
$$

Its Gaussian integral in the intermediate variable gives the
semigroup identity, and differentiation gives
$\partial_tM_\kappa=-H_\kappa M_\kappa$. As $t\downarrow0$
it has the Euclidean heat approximate-identity limit; these properties
identify the oscillator Friedrichs semigroup. At $Y=0$ its Gaussian
parameters $A=\kappa/(4\pi\sinh(\kappa t))$ and
$B=\kappa\coth(\kappa t)/4$ satisfy
$A'/A=-4B$ and $B'=\kappa^2/4-4B^2$, with
$A\sim(4\pi t)^{-1}$ and $B\sim(4t)^{-1}$.
This proves (9.7) for $k\ne0$, and the ordinary two-dimensional
Gaussian gives the zero mode. Both whole-group heat kernels are
nonnegative and invariant under horizontal rotations. Their horizontal
projection is the semigroup with generator $\Delta_X$, since the
fields on functions independent of $z$ reduce to $\partial_x,\partial_y$.
Consequently their $z$ marginal is exactly the Gaussian in (9.7),
and $h_\epsilon(t,\rho,\cdot)\in L^1(\mathbb R)$.
This also justifies the Fourier columns as ordinary integrals.
The factors $\kappa t$, $e^{-tk^2}$ and $(4\pi t)^{-1}$ retain
the stated clock and the Lebesgue unit source.

Now let $u\in C_c^\infty(\mathbb R^3;\mathbb C)$ be arbitrary,
and use normalized angular averaging $\langle\cdot\rangle_\vartheta$
to construct

$$
w(\rho,z)=\big\langle |u(\rho,\vartheta,z)|^2
                         \big\rangle_\vartheta^{1/2},
\qquad
D=\rho^{-1}\partial_\vartheta+\tfrac\rho2\partial_z.
\tag{9.11}
$$

For $\rho>0$ the horizontal energy density is
$|u_\rho|^2+|Du|^2$. Where $w>0$, the norm derivative and periodicity
give

$$
\begin{aligned}
w w_\rho&=\operatorname{Re}\langle\overline u u_\rho\rangle_\vartheta,
 &w w_z&=\operatorname{Re}\langle\overline u u_z\rangle_\vartheta,\\
\operatorname{Re}\langle\overline u u_\vartheta\rangle_\vartheta&=0,
 &\tfrac\rho2 w w_z
    &=\operatorname{Re}\langle\overline u Du\rangle_\vartheta,\\
|w_\rho|^2&\le\langle|u_\rho|^2\rangle_\vartheta,
 &\tfrac{\rho^2}{4}|w_z|^2&\le\langle|Du|^2\rangle_\vartheta.
\end{aligned}
\tag{9.12}
$$

These are Cauchy–Schwarz inequalities. The weak norm chain rule gives
the same inequalities almost everywhere on the zero set of $w$, and
also $|w_z|^2\le\langle|u_z|^2\rangle_\vartheta$.
For a global regularity justification, regard $w(X,z)$ as the norm
of the Hilbert-valued map $\vartheta\mapsto u(R_\vartheta X,z)$,
where $R_\vartheta$ is planar rotation. The Lipschitz norm map
shows directly that its radial extension is compactly supported
Euclidean $H^1(\mathbb R^3)$, with no boundary condition at the axis.
Smooth approximation in Euclidean $H^1$ with support in a fixed compact
set then gives $w\in\mathcal H_1$, because the frame coefficients
are bounded there. Integrating (9.12) with $2\pi\rho\,d\rho\,dz$
and using rotation invariance of $\mathcal G_1$ yields

$$
\mathcal E_H[w]\le\mathcal E_H[u],\qquad
\int\mathcal G_1|w|^2\,d\xi=\int\mathcal G_1|u|^2\,d\xi.
\tag{9.13}
$$

The weighted identity follows directly from Tonelli; it does not
restrict the angular modes of the initial input.

Apply (9.4) to $w$, and define a second auxiliary function by

$$
F(\rho,k)=\widehat w(\rho,k),\qquad
\psi(\rho,k)=|F(\rho,k)|,\qquad
v(\rho,z)=\frac1{2\pi}\int_{\mathbb R}e^{ikz}\psi(\rho,k)\,dk.
\tag{9.14}
$$

Initially the inverse is understood in $L^2$. Since $w$ is Euclidean
$H^1$, its partial transform has square-integrable horizontal
derivatives and $kF\in L^2$. The Sobolev modulus rule contracts those
derivatives and preserves $k^2|F|^2$. Thus $v$ is Euclidean $H^1$,
is radial in $X$ and has the same bounded horizontal support as $w$.
For radial functions the exact horizontal energy is

$$
\mathcal E_H[w]
 =2\pi\int_0^\infty\int_{\mathbb R}
    \rho\big(|w_\rho|^2+\rho^2|w_z|^2/4\big)\,dz\,d\rho.
\tag{9.15}
$$

Plancherel and $|\partial_\rho|F||\le|\partial_\rho F|$
almost everywhere show $\mathcal E_H[v]\le\mathcal E_H[w]$;
the $\rho^2 k^2$ term is unchanged. For membership in the original
closure, cut off the $z$ tail of $v$ and then mollify in Euclidean
$H^1$, keeping horizontal support in a fixed larger box. The
coefficients of $U,V,Z_H$ are bounded on that box, independently of
$z$. The cutoff errors are bounded by a constant times
$N^{-1}\|v\|_2$, and the derivative tails tend to zero. Hence

$$
v\in\mathcal H_1,\qquad
\mathcal E_H[v]\le\mathcal E_H[w].
\tag{9.16}
$$

No compact central support or smoothness of $v$ is required.

For almost every $\rho>0$, $w(\rho,\cdot)\in H^1(\mathbb R)$.
Cauchy–Schwarz with $(1+k^2)^{-1}$ gives

$$
\int_{\mathbb R}|F(\rho,k)|\,dk
 \le\left(\int_{\mathbb R}(1+k^2)|F(\rho,k)|^2\,dk\right)^{1/2}
     \left(\int_{\mathbb R}\frac{dk}{1+k^2}\right)^{1/2}<\infty.
\tag{9.17}
$$

Thus both inversions in (9.14) are also ordinary absolutely convergent
inversions at those radii. For each $t>0$, Fourier inversion and the
$L^1_z$ marginal of the heat kernel give

$$
\int_{\mathbb R}h_\epsilon(t,\rho,z)|w(\rho,z)|^2\,dz
 =\frac1{(2\pi)^2}\iint_{\mathbb R^2}
 q_\epsilon(t,\rho,k-\ell)
 F(\rho,k)\overline{F(\rho,\ell)}\,dk\,d\ell.
\tag{9.18}
$$

The evenness of $q_\epsilon$ removes the sign from the inverse
Fourier exponents. This is an absolutely convergent identity:
$|q_\epsilon|\le\|h_\epsilon(t,\rho,\cdot)\|_1$ and (9.17)
bound the absolute double integral. The left side is nonnegative.
Taking the absolute value on the right and using the nonnegative
ordering in (9.7) bounds it, for $\epsilon=1$, by

$$
\begin{aligned}
&\frac1{(2\pi)^2}\iint q_0(t,\rho,k-\ell)
                     \psi(\rho,k)\psi(\rho,\ell)\,dk\,d\ell\\
&\hspace{30mm}=\int_{\mathbb R}h_0(t,\rho,z)|v(\rho,z)|^2\,dz.
\end{aligned}
\tag{9.19}
$$

The last equality is the same absolutely convergent inversion formula
for $\psi$. Integrate this nonnegative fixed-time inequality against
$2\pi\rho\,d\rho$ and then over every $0<t<\infty$. Tonelli,
or increasing finite time intervals, gives the full comparison

$$
\int\mathcal G_1|w|^2\,d\xi
       \le\int\mathcal G_0|v|^2\,d\xi<\infty.
\tag{9.20}
$$

Finiteness follows from (9.6) and (9.16). There is no exchange of a
signed infinite-time Fourier integral: absolute convergence was used
at fixed time, and the subsequent integration has nonnegative
integrands. Both time endpoints and all spatial tails are retained.
This is a comparison after transforming the test function; it makes
no assertion of pointwise domination $\mathcal G_1\le\mathcal G_0$.

Combining the established inequalities in their indicated directions,

$$
\begin{aligned}
\mathcal T_1[u]&\ge\mathcal E_H[u]
 \ge\mathcal E_H[w]\ge\mathcal E_H[v]\\
&\ge K\int\mathcal G_0|v|^2\,d\xi
 \ge K\int\mathcal G_1|w|^2\,d\xi
 =K\int\mathcal G_1|u|^2\,d\xi.
\end{aligned}
\tag{9.21}
$$

Finally, for arbitrary complex $u\in\mathcal H_1$, take its defining
compact smooth core sequence $u_j$. It converges in $L^2$ and in
all three derivative norms, so $\mathcal T_1[u_j]\to\mathcal T_1[u]$.
Along an almost-everywhere convergent subsequence Fatou and (9.21)
give

$$
K\int\mathcal G_1|u|^2\,d\xi
 \le\liminf_j K\int\mathcal G_1|u_j|^2\,d\xi
 \le\lim_j\mathcal T_1[u_j]=\mathcal T_1[u].
\tag{9.22}
$$

For $u=0$ both sides vanish. The argument uses neither an optimizer
nor equality of different form domains. $\square$

**Theorem 9.3 (threshold identity and the original response consumers).**
The constants of Definition 1.1 and C, Definition 16.2, satisfy

$$
\Lambda_*=2\pi\lambda_0,\qquad
 g_*=g_{\mathrm c}=2\pi m_0\lambda_0,\qquad m_0=(2r)^{-1}.
\tag{9.23}
$$

Consequently the uniform shifted realization, positive response,
rank estimates and resolvent reconstruction of Theorems 1.2,
2.2–2.3 and 3.1 hold on their original domains and with their stated
shift and parameter conditions for the entire coupling interval
$0\le g\le g_{\mathrm c}$, including $g=g_{\mathrm c}$.
At zero noise the critical bulk domain is the ground-transform
completion (1.8); at positive noise it remains the corresponding
free domain. The trace domain remains exactly (1.4).
For $g>g_{\mathrm c}$ Theorem 5.1 excludes a common fixed shift
with a positive minimizing response down to arbitrarily small
positive noise, in exactly its stated sense.

Proof. C, Definition 16.2, gives finite strictly positive denominators
for every nonzero $u\in\mathcal H_1$. Dividing (9.5) by that
denominator and taking the infimum yields $\Lambda_*\ge K$.
The annular upper bound of C, Theorem 16.3, gives
$\Lambda_*\le2\pi\lambda_0=K$. This proves (9.23) without
attainment of the quotient. Substitution into (1.2) makes the original
range $0\le g\le g_*$ exactly $0\le g\le g_{\mathrm c}$.
Thus (1.3)–(1.4), (2.2)–(2.4), (2.6)–(2.7) and (3.1)–(3.2)
apply with their same shifts, raw complex forcing unit ball,
normalizations and domains. In particular the rank orders remain
$\eta^{-3}$ at zero noise and $\epsilon^{-1}\eta^{-2}$ below positive
noise, with the crossover and endpoint strictness already specified
in Theorem 2.3. This substitution neither diagonalizes the attractive
operator nor changes the exact killed inverse retained in (3.1).
The domain distinction is precisely Theorem 1.2's distinction at the
now included endpoint, not a new domain identification. Finally
$g>g_{\mathrm c}$ is now exactly $g>g_*$, so Theorem 5.1 applies.
The small-coupling inverse of Theorems 6.2–8.1 retains its existing
hypotheses and does not supply an unshifted critical response. $\square$

**Definition 9.4 (mathematical suppliers and scope of the comparison).**
The horizontal sharp inequality, its natural endpoint domain and
$\mathcal G_0=(2\pi)^{-1}R^{-2}$ in (9.6) are the exact inputs of
V, Definition 10.1 and Theorem 10.2. C, Definition 16.2 and
Theorem 16.3, supply denominator positivity and finiteness and the
opposite annular bound used in (9.23). Fourier inversion, Plancherel,
the Sobolev modulus chain rule and the oscillator Mehler formula are
classical intermediate ingredients; (9.8)–(9.10) fix their magnetic
source-column correspondence and normalization here. For the Mehler
formula see also S. Thangavelu, *Lectures on Hermite and Laguerre
Expansions*, Chapter 1. Fourier-majorant arguments are discussed in
Lenzmann–Sok, [*A sharp rearrangement principle in Fourier space and
symmetry results for PDEs with arbitrary order*, §5, Lemma 5.1](https://arxiv.org/html/1805.06294v3).
That unweighted upper-majorant result is not a supplier of the
weighted magnetic comparison (9.18)–(9.20), and no symmetric decreasing
rearrangement is invoked here. The source-relative additional
comparison is the combination of the rotation norm (9.11), central
Fourier modulus (9.14), ordered exact heat columns (9.7) and the
full-time passage (9.20); the sharp horizontal input is reused.
These attributions do not assert global literature priority.

The conclusion concerns the original analytic attractive family.
It adds no quotient optimizer, no new trace condition and no
identification of the zero-noise completed bulk domain with a
positive-noise free domain. The common fixed-shift exclusion above
$g_{\mathrm c}$ leaves noise-dependent shifts and indefinite or
meromorphic response constructions outside that exclusion. Neither
(9.5) nor (9.23) supplies a physical forcing or actuator, a common-source
physical realization, a different native process or clock, or a
physical spatial dimension. Such a realization still requires the
separate correspondence specified in Definitions 5.2 and 8.2.

## 追加锚（本行以下为增补区）

## 10. Sharp central remainder and nonattainment

**Definition 10.1 (the fixed full-Green quotient).** Retain exactly
Definition 9.1's complex closure $\mathcal H_1$, fields $U,V,Z_H$,
Lebesgue measure and natural angular constant $K=2\pi\lambda_0$.
Write

$$
W[u]=\int_{\mathbb R^3}\mathcal G_1(\xi)|u(\xi)|^2\,d\xi,
\qquad Q[u]=\frac{\mathcal T_1[u]}{W[u]}\quad(0\ne u\in\mathcal H_1).
\tag{10.1}
$$

Here $\mathcal G_1=\int_0^\infty h_1(t,\cdot)\,dt$ is the
original-clock Lebesgue unit-source Green field of (9.2), with both
time endpoints retained. C, Definition 16.2, gives $0<W[u]<\infty$
for every nonzero $u\in\mathcal H_1$.

**Corollary 10.2 (optimal central coefficient and no extremizer).**
For every complex $u\in\mathcal H_1$, including zero and with no
angular symmetry assumption,

$$
\mathcal T_1[u]-K W[u]\ge\|Z_Hu\|_2^2.
\tag{10.2}
$$

The central coefficient one is optimal even on the compact smooth
core: for every real $c>1$ there is a nonzero
$u\in C_c^\infty(\mathbb R^3;\mathbb C)$ such that

$$
\mathcal T_1[u]-K W[u]<c\|Z_Hu\|_2^2.
\tag{10.3}
$$

Moreover,

$$
\mathcal T_1[u]>K W[u]\quad(0\ne u\in\mathcal H_1),
\qquad \inf_{0\ne u\in\mathcal H_1}Q[u]=K.
\tag{10.4}
$$

Thus the sharp quotient has no nonzero $\mathcal H_1$ extremizer.
Every normalized minimizing sequence $W[u_n]=1$,
$\mathcal T_1[u_n]\to K$ necessarily satisfies

$$
\|Z_Hu_n\|_2^2\le\mathcal T_1[u_n]-K\longrightarrow0.
\tag{10.5}
$$

Proof. For arbitrary complex compact smooth $u$, the chain (9.21),
starting at $\mathcal E_H[u]$, already gives
$\mathcal E_H[u]\ge K W[u]$. Its auxiliary rotation norm and Fourier
modulus impose no restriction on the original $u$. For any
$u\in\mathcal H_1$, choose its defining compact smooth approximation
$u_j$. Then $u_j\to u$ in $L^2$, all three closed derivatives
converge in $L^2$, and $\mathcal E_H[u_j]\to\mathcal E_H[u]$.
Along an almost-everywhere convergent subsequence, the nonnegativity
of $\mathcal G_1$ and Fatou's lemma give

$$
K W[u]\le\liminf_j K W[u_j]\le\mathcal E_H[u].
\tag{10.6}
$$

This proves weighted finiteness on the entire closure independently
of C, (15.8). Adding the closed central energy proves (10.2), also
for $u=0$.

To identify that central derivative, let $g$ be the $L^2$ limit of
$\partial_z u_j$. Integration by parts against any
$\eta\in C_c^\infty(\mathbb R^3;\mathbb C)$ yields

$$
\int g\,\overline\eta\,d\xi
 =\lim_j\int\partial_z u_j\,\overline\eta\,d\xi
 =-\lim_j\int u_j\,\overline{\partial_z\eta}\,d\xi
 =-\int u\,\overline{\partial_z\eta}\,d\xi.
\tag{10.7}
$$

Hence the closed $Z_Hu$ is exactly the distributional derivative
$\partial_z u$. If $Z_Hu=0$, convolve $u$ in Euclidean coordinates
with any compact smooth approximate identity $\varphi_\delta$.
The function $u\ast\varphi_\delta$ is smooth, lies in $L^2$ by Young's
inequality, and has zero $z$ derivative, so it is independent of $z$.
Fubini on the infinite-measure central line forces this $L^2$
function to vanish. Since $u\ast\varphi_\delta\to u$ in $L^2$, we
obtain $u=0$. In particular $\|Z_Hu\|_2^2>0$ for every nonzero
member of the actual closure. This argument makes no identification
of $\mathcal H_1$ with Euclidean $H^1$.

For sharpness choose nonzero $a\in C_c^\infty(\mathbb R^2;\mathbb C)$
and $b\in C_c^\infty(\mathbb R;\mathbb C)$ with $b'\not\equiv0$.
Put $\phi(X,z)=a(X)b(z)$,
$A=\mathcal E_H[\phi]\ge0$ and
$B=\|Z_H\phi\|_2^2=\|a\|_2^2\|b'\|_2^2>0$.
For $s>0$ set $\delta_s(X,z)=(sX,s^2z)$ and
$u_s=\phi\circ\delta_{1/s}$. Every $u_s$ is a nonzero compact
smooth test. The exact fields in (9.1) give

$$
\begin{aligned}
Uu_s&=s^{-1}(U\phi)\circ\delta_{1/s},&
Vu_s&=s^{-1}(V\phi)\circ\delta_{1/s},\\
Z_Hu_s&=s^{-2}(Z_H\phi)\circ\delta_{1/s},&
\det D\delta_s&=s^4,\\
\mathcal E_H[u_s]&=s^2 A,&\|Z_Hu_s\|_2^2&=B.
\end{aligned}
\tag{10.8}
$$

Given $c>1$, choose $s^2=(c-1)B/[2(A+B)]>0$.
By (10.6), $W[u_s]$ is finite, and its nonnegativity implies

$$
\mathcal T_1[u_s]-K W[u_s]\le B+s^2 A
 \le B+\tfrac12(c-1)B<cB.
\tag{10.9}
$$

This proves (10.3). No homogeneity, pole regularity or asymptotic
formula for $\mathcal G_1$ is used; its clock, source and full-time
integral are unchanged.

For nonzero $u$, (10.2) and the zero-kernel argument give the strict
inequality in (10.4). The positive denominator supplied by C,
Definition 16.2, permits division. Theorem 9.3, using C, Theorem
16.3's annular upper bound, already supplies the infimum $K$.
Consequently it is attained by no nonzero member of $\mathcal H_1$.
Finally (10.2) gives (10.5) directly. $\square$

The Fatou passage, distributional integration by parts, Young's
inequality and approximate-identity convergence used in this proof
are classical measure and convolution arguments; see G. B. Folland,
*Real Analysis*, second edition, Chapters 2 and 8. The dilation
identities (10.8) use only the fields of Definition 9.1. The
source-specific optimal-coefficient and nonattainment conclusions
are repo-derived consequences of (9.21), Theorem 9.3 and the positive
Green denominator in C, Definition 16.2; they assert no historical
priority. The vanishing in (10.5) is only a necessary central-energy
condition, with no profile convergence or compactness conclusion.
All statements concern the whole-group $\mathcal H_1$ closure;
they give no slab extremizer statement, zero-noise completed-domain
identification, physical realization or additional response rank law.

## 追加锚（本行以下为增补区）
