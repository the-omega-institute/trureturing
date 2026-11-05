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

## 10. Higher-contact self-fields and their actual three-coordinate marginal

**Definition 10.1 (one source before and after retention).** Let
$n\ge1$ be an integer. On $H^n=\mathbb R^{2n}\times\mathbb R$ use
the group law
$(X,z)(X',z')=(X+X',z+z'+\tfrac12\sum_j(x_jy'_j-y_jx'_j))$,
raw Lebesgue measure $dp=dX\,dz$, identity pole $0$, and

$$
\begin{aligned}
 U_j&=\partial_{x_j}-\tfrac{y_j}{2}\partial_z,&
 V_j&=\partial_{y_j}+\tfrac{x_j}{2}\partial_z,&Z&=\partial_z,\\
 L_{n,\epsilon}&=-\sum_{j=1}^n(U_j^2+V_j^2)-\epsilon^2Z^2,&
 T_{n,\epsilon}[u]&=\sum_j(\|U_ju\|_2^2+\|V_ju\|_2^2)
                         +\epsilon^2\|Zu\|_2^2,\\
 h_{n,\epsilon}(t,p)&=e^{-tL_{n,\epsilon}}\delta_0(p),&
 G_{n,\epsilon}(p)&=\int_0^\infty h_{n,\epsilon}(t,p)\,dt .
\end{aligned}
\tag{10.1}
$$

The free operator is the Friedrichs operator of the compact smooth
complex core. Its clock has horizontal covariance $2$ and central
independent covariance $2\epsilon^2$. Write $X=(X_1,W)$, where
$X_1=(x_1,y_1)$, $W\in\mathbb R^{2n-2}$, and put
$\xi=(X_1,z)$, $\rho=|X_1|$, $\pi(X,z)=\xi$. Define the actual
pole-started marginal densities and their complete occupation field by

$$
 m_{n,\epsilon}(t,\xi)=\int h_{n,\epsilon}(t,X_1,W,z)\,dW,
 \qquad M_{n,\epsilon}(\xi)=\int G_{n,\epsilon}(X_1,W,z)\,dW.
\tag{10.2}
$$

When $n=1$ the empty fibre integral is the identity, so
$h_{1,\epsilon}=h_\epsilon$ and $G_{1,\epsilon}=\mathcal G_\epsilon$
in (9.2), with the evident extension to every $\epsilon\ge0$.
The retained reference kinetic energy is $\mathcal E_H$ of (9.1).
Its full complex horizontal free domain is $\mathcal H_0$ of
Definition 9.1; the unit-central-noise free domain
$\mathcal H_1$ is a subspace of it. For positive $\epsilon$, the
free closure of $\mathcal E_H+\epsilon^2\|Zf\|_2^2$ has the same
set of members as $\mathcal H_1$, with equivalent norms for each
fixed positive $\epsilon$. None of these domains is identified with
an isotropic Euclidean Sobolev space or with a critical attractive
completion.

For a parent-domain comparison fix, once and for all, a connected
smooth relatively compact open set $D\subset H^n$ containing $0$.
Let $h^D_{n,\epsilon}(t,0,p)$ be the Dirichlet free heat kernel of
the same operator, density and clock, and set
$G^D_{n,\epsilon}(p)=\int_0^\infty h^D_{n,\epsilon}(t,0,p)dt$.
Every shrinking test below uses this one original field on $D$.

**Theorem 10.2 (stable retained field, nonautonomous retention and full
self-field collapse).** With the source of Definition 10.1, the
following assertions hold jointly.

For every $n\ge1$, $\epsilon\ge0$ and $t>0$, the central Fourier
transform, in convention (9.4), is

$$
 \widehat m_{n,\epsilon}(t,\rho,k)
   =q_\epsilon(t,\rho,k)\operatorname{sech}(|k|t)^{n-1},
 \qquad \widehat m_{n,\epsilon}(t,\rho,0)
   =(4\pi t)^{-1}e^{-\rho^2/(4t)}.
\tag{10.3}
$$

Here $q_\epsilon$ is exactly (9.7), with its displayed scalar
$e^{-\epsilon^2tk^2}$. These are probability densities. Set
$a_t(z)=(2t)^{-1}\operatorname{sech}(\pi z/(2t))$, and let
$\varphi_{\epsilon,t}$ be the central Gaussian of variance
$2\epsilon^2t$, interpreted as $\delta_0$ at $\epsilon=0$.
The exact complete-time marginal is

$$
\begin{aligned}
 M_{n,\epsilon}(\rho,z)
  &=\int_0^\infty
       [h_{1,\epsilon}(t,\rho,\cdot)*a_t^{*(n-1)}](z)\,dt\\
  &=\int_0^\infty
       [\varphi_{\epsilon,t}*m_{n,0}(t,\rho,\cdot)](z)\,dt.
\end{aligned}
\tag{10.4}
$$

All convolutions in (10.4) are in the central real variable; a zeroth
convolution power is $\delta_0$. The field is positive and finite
off $\xi=0$, belongs to $L^1_{\rm loc}(\mathbb R^3)$, and has
infinite total Lebesgue integral. At zero noise, for $n\ge2$, it has
the explicit absolutely convergent fibre formula

$$
\begin{aligned}
 c_n&=\frac{2^{n-2}\Gamma(n/2)^2}{\pi^{n+1}},\\
 M_{n,0}(\rho,z)
  &=\frac{c_n\pi^{n-1}}{\Gamma(n-1)}
       \int_0^\infty
       \frac{s^{n-2}\,ds}{((\rho^2+s)^2+16z^2)^{n/2}},\\
 M_{n,0}(aX_1,a^2z)&=a^{-2}M_{n,0}(X_1,z)\qquad(a>0).
\end{aligned}
\tag{10.5}
$$

For every $n\ge1$, every fixed $\epsilon\ge0$, and every complex
$f\in\mathcal H_0$, in particular every $f\in\mathcal H_1$,

$$
 \mathcal E_H[f]\ \ge\ K\int M_{n,\epsilon}|f|^2\,d\xi,
 \qquad K=2\pi\lambda_0>0.
\tag{10.6}
$$

Thus $\mathcal E_H-g\int M_{n,\epsilon}|f|^2\ge0$ for
$0\le g\le K$. The constant is a sufficient bound; no sharpness
for $n>1$ is asserted.

For $n\ge2$, $\pi$ is not an all-start same-clock Markov factor.
The densities $m_{n,\epsilon}(t)$ do not form a convolution
semigroup on the retained $H^1$, and $M_{n,\epsilon}$ is not a
constant multiple of $G_{1,\epsilon}$, even for a fixed positive
$\epsilon$. Nevertheless, for every fixed $\epsilon\ge0$ and $g>0$,

$$
\begin{aligned}
 \inf_{\substack{u\in C_c^\infty(H^n\setminus\{0\};\mathbb C)\\
                         \|u\|_{L^2(dp)}=1}}
       \left(T_{n,\epsilon}[u]-g\int G_{n,\epsilon}|u|^2dp\right)
       &=-\infty,\\
 \inf_{\substack{u\in C_c^\infty(D\setminus\{0\};\mathbb C)\\
                         \|u\|_{L^2(dp)}=1}}
       \left(T_{n,\epsilon}[u]-g\int G^D_{n,\epsilon}|u|^2dp\right)
       &=-\infty .
\end{aligned}
\tag{10.7}
$$

Consequently no finite shift makes the original parent attractive
energy a positive minimizing response on any domain containing this
zero-trace core. In particular its unnormalized zero-trace infimum
is $-\infty$ after every finite shift. These are fixed-noise
assertions, without constants uniform as $\epsilon\downarrow0$.

Proof. The classical $2n$-dimensional magnetic source column is the
product of the $n$ oscillator columns used in (9.7)–(9.10):

$$
 \widehat h_{n,\epsilon}(t,X,k)
 =e^{-\epsilon^2tk^2}
   \left(\frac{\kappa}{4\pi\sinh(\kappa t)}\right)^n
       e^{-\kappa|X|^2\coth(\kappa t)/4},\qquad \kappa=|k|.
\tag{10.8}
$$

The limit at $k=0$ is the ordinary $2n$-dimensional Gaussian.
The radial pole column removes the magnetic angular terms, rather
than removing them on arbitrary tests. The direct-integral closure
and source approximation are precisely the product version of the
argument for (9.8)–(9.10). Integration of each omitted pair gives
$\int_{\mathbb R^2}(\kappa/(4\pi\sinh\kappa t))
e^{-\kappa|w|^2\coth(\kappa t)/4}dw
=1/\cosh(\kappa t)$. This proves (10.3), including its zero mode.
The full horizontal projection is the ordinary $2n$-dimensional
Gaussian; its fixed-$X$ central rows are integrable. This and
nonnegativity justify the fibre Fubini passage.
The characteristic function of $a_t$ is $\operatorname{sech}(tk)$;
Fourier uniqueness proves (10.4) at each fixed time, and Tonelli
then proves the complete Green marginal.
These oscillator factors are the classical ones in Krötz–Thangavelu–Xu,
[*The heat kernel transform for the Heisenberg group*, §2.2,
(2.2.1)](https://arxiv.org/html/math/0401243v2). Their Laplace element
includes $Z^2$. Here the central coefficient is $\epsilon^2$ and
the inverse Fourier factor is $1/(2\pi)$ as in (9.4); the Gaussian
zero mode fixes the Lebesgue unit source, independently of a printed
inverse-transform prefactor.

Here are bounds justifying the time endpoints and fibre integrals.
Inverting (10.3) at $\epsilon=0$ and shifting the rescaled contour
$tk$ to $v+i\alpha\operatorname{sgn}z$, $0<\alpha<\pi/2$, gives

$$
 0\le m_{n,0}(t,\rho,z)
       \le C_n t^{-2}e^{-c_n'(\rho^2+|z|)/t}.
\tag{10.9}
$$

Indeed $v/\sinh v$ and $\operatorname{sech}(v)^{n-1}$ are analytic
in the shifted strip, their product decays exponentially on its
horizontal lines, and
$\operatorname{Re}[(v+i\alpha)\coth(v+i\alpha)]$
is bounded below by a positive number. The latter follows directly
from $(v\sinh(2v)+\alpha\sin(2\alpha))
/(\cosh(2v)-\cos(2\alpha))$, which is positive and tends to
$|v|$ at infinity. The vertical contour ends vanish. The same contour
in (10.8) bounds $h_{n,0}$ by
$Ct^{-n-1}e^{-c(|X|^2+|z|)/t}$; central Gaussian convolution gives
$h_{n,\epsilon}$. Thus the full Green integrals are also finite off
their pole. At positive noise convolve (10.9) with
$\varphi_{\epsilon,t}$. For $z\ne0$
split its integral at $|s|=|z|/2$ to bound its central factor by

$$
 e^{-c_n'|z|/(2t)}
       +C\frac{\sqrt t}{\epsilon}e^{-z^2/(16\epsilon^2t)}.
\tag{10.10}
$$

For $\rho\ne0$ the factor $e^{-c_n'\rho^2/t}$ alone suffices.
These estimates give an integrable small-time bound on off-pole
compact sets. They also give such a bound uniformly for
$0\le\epsilon\le E$ on each fixed off-pole compact set: on a
$z$-separated set the supremum of
$\epsilon^{-1}e^{-z^2/(16\epsilon^2t)}$ is bounded, for small $t$,
by $C_E e^{-z^2/(32E^2t)}$. The zero-noise case is (10.9).
For large times $m_{n,\epsilon}\le C_nt^{-2}$, also after central
convolution. Thus (10.4) is finite and continuous off the pole, and
$M_{n,\epsilon}\to M_{n,0}$ locally uniformly there as
$\epsilon\downarrow0$. Positivity follows from the positive heat
kernel. For local spatial integrability, integrate the mass-one
density over $0<t<1$ and the $t^{-2}$ bound over $t\ge1$ on a
compact set. For total mass, Tonelli gives $\int_0^\infty1\,dt=\infty$.
No central Fourier transform of the full Green field at the zero
mode is asserted; its time integral at that mode diverges.

The classical horizontal fundamental solution in these fields is
$G_{n,0}(X,z)=c_n(|X|^4+16z^2)^{-n/2}$. Its gauge shape is the
Folland solution recalled in Kombe,
[*Sharp Hardy type inequalities on the Carnot Group*, §3](https://arxiv.org/html/math/0501522v1),
under the central-coordinate change $t_{\rm Kombe}=-4z$.
The coefficient used here is fixed directly by unit flux in $dp$:
for $R_n=(|X|^4+16z^2)^{1/4}$,
$|\nabla_HR_n|^2=|X|^2/R_n^2$, and the outward flux of
$-\nabla_H(cR_n^{-2n})$ through $R_n=1$ equals
$c\,n\pi^n\Gamma(n)^{-1}\int_{-\pi/2}^{\pi/2}\cos^n a\,da$.
Setting this equal to one gives exactly $c=c_n$ in (10.5).
Integrating the heat equation gives the same unit-source relation
for the heat integral. The preceding heat bound gives its decay at
infinity. The difference from the gauge solution is globally smooth
by hypoellipticity, harmonic and decaying, hence zero by the maximum
principle. This identifies the actual heat integral with that
fundamental solution. Polar integration in $W$, with
$s=|W|^2$ and $dW=\pi^{n-1}s^{n-2}ds/\Gamma(n-1)$, proves
(10.5). Its integrand is $O(s^{-2})$ at infinity and is integrable
at zero whenever $\xi\ne0$. Changing $s$ to $a^2s$ proves its
degree $-2$ for the retained $H^1$ dilation. In particular this
degree differs from the full field's degree $-2n$.

There is a concrete obstruction to rescaling the retained field to
the native one. Beta integration in (10.5) gives, for $n\ge2$,

$$
\begin{aligned}
 M_{n,0}(\rho,0)&=A_n\rho^{-2},&
 A_n&=\frac{2^{n-2}\Gamma(n/2)^2}{\pi^2\Gamma(n)},\\
 M_{n,0}(0,z)&=\frac1{8\pi|z|},&
 2\pi A_n&=\frac{\Gamma(n/2)}{\sqrt\pi\Gamma((n+1)/2)}<1.
\end{aligned}
\tag{10.11}
$$

The strict inequality follows from
$B(n/2,1/2)<B(1/2,1/2)=\pi$. But
$G_{1,0}(\rho,0)=(2\pi\rho^2)^{-1}$ and
$G_{1,0}(0,z)=(8\pi|z|)^{-1}$. The two axis ratios disagree.
In particular the first higher-contact case has

$$
 M_{2,0}(\rho,z)=\frac{\arctan(4|z|/\rho^2)}{4\pi^2|z|},
 \qquad M_{2,0}(\rho,0)=\frac1{\pi^2\rho^2},
\tag{10.12}
$$

with continuous off-pole axis values: its ratios are $1$ and
$2/\pi$. For positive noise the exact heat scaling gives
$M_{n,\epsilon}(aX_1,a^2z)=a^{-2}M_{n,\epsilon/a}(X_1,z)$;
the same formula holds for $G_{1,\epsilon}$. If the two fixed-noise
fields were proportional, letting $a\to\infty$ and using the
locally uniform zero-noise limit just proved would contradict
(10.11). This uses actual axis values, not homogeneity alone.

The dynamics obstruction also preserves the original source map.
Put $A_{n,\epsilon}=-L_{n,\epsilon}$. For a smooth bounded retained
function $F$ one has locally

$$
 A_{n,\epsilon}(F\circ\pi)(X_1,W,z)
   =A_{1,\epsilon}F(X_1,z)+\frac{|W|^2}{4}F_{zz}(X_1,z).
\tag{10.13}
$$

Take $F=z^2$ near $\xi=0$, with a compact retained cutoff.
The two starts $p=0$ and $p'=(X_1=0,x_2=1,
y_2=0,\text{other }W=0,z=0)$ have identical $\pi$ values, but
the derivatives at time zero of their expectations of $F\circ\pi$
differ by $1/2$. This contradicts any all-start factor identity.
For the pole-started kernels themselves, central convolution commutes
with $H^1$ convolution, so (10.4) at fixed time gives

$$
 m_{n,\epsilon}(s)*_{H^1}m_{n,\epsilon}(t)
  =h_{1,\epsilon}(s+t)*_z a_s^{*(n-1)}*_z a_t^{*(n-1)}.
\tag{10.14}
$$

Its Fourier column has scalar factor
$[\operatorname{sech}(|k|s)\operatorname{sech}(|k|t)]^{n-1}$,
whereas $m_{n,\epsilon}(s+t)$ has
$\operatorname{sech}(|k|(s+t))^{n-1}$. They are unequal for
$s,t>0$, $k\ne0$. Thus the retained family is neither the native
semigroup nor another $H^1$ convolution semigroup. It is not an
additive $\mathbb R^3$ convolution semigroup either: its central
characteristic function is
$e^{-\epsilon^2tk^2}\operatorname{sech}(|k|t)^n$, which fails
the multiplicative time law.

To prove the positive form bound, start with arbitrary complex
$f\in C_c^\infty(\mathbb R^3)$. Use exactly the two auxiliary
functions $w,v$ of (9.11)–(9.16). Rotation invariance of $M$ gives
$\int M|f|^2=\int M|w|^2$, and
$\mathcal E_H[v]\le\mathcal E_H[w]\le\mathcal E_H[f]$.
Both auxiliaries belong to $\mathcal H_1$, as proved there.
For almost every $\rho>0$, (9.17) makes the fixed-time double
Fourier integrals absolutely convergent. In (9.18) replace
$q_\epsilon$ by the column (10.3). Since

$$
 0\le q_\epsilon(t,\rho,k-\ell)
          \operatorname{sech}(|k-\ell|t)^{n-1}
       \le q_0(t,\rho,k-\ell),
\tag{10.15}
$$

taking the modulus of the transformed test coefficients bounds
$\int m_{n,\epsilon}(t,\rho,z)|w(\rho,z)|^2dz$ by
$\int h_{1,0}(t,\rho,z)|v(\rho,z)|^2dz$.
Integrate this nonnegative inequality first in $2\pi\rho\,d\rho$
and then in all $t>0$. Tonelli and (9.6) give

$$
 \int M_{n,\epsilon}|f|^2d\xi
  \le\int G_{1,0}|v|^2d\xi
  \le K^{-1}\mathcal E_H[v]
  \le K^{-1}\mathcal E_H[f].
\tag{10.16}
$$

For arbitrary $f\in\mathcal H_0$ use its defining smooth core
sequence, convergence of the horizontal derivative norms, an
almost-everywhere convergent subsequence and Fatou. This proves
(10.6), including finiteness of the weighted integral and $f=0$.
There is no symmetry restriction on the original complex test,
no signed infinite-time Fourier exchange, and no inference of a
pointwise Green ordering from (10.15).

It remains to compare this retained bound with the full own-field
energies. At zero noise let $Q_n=2n+2$ and
$\delta_a(X,z)=(aX,a^2z)$. For a fixed normalized nonzero complex
$u\in C_c^\infty(H^n\setminus\{0\})$, homogeneous scaling gives

$$
 u_a=a^{-Q_n/2}u\circ\delta_{1/a},\qquad
 T_{n,0}[u_a]=a^{-2}T_{n,0}[u],\qquad
 \int G_{n,0}|u_a|^2dp=a^{-2n}\int G_{n,0}|u|^2dp>0.
\tag{10.17}
$$

The final integral before multiplication by $a^{-2n}$ is positive
and finite. For $n\ge2$ the negative term dominates as $a\downarrow0$.
This is the familiar $Q>4$ concentration intermediate, also used in
[Recursive holographic boundary geometry, continuation III,
Proposition 82.2](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md).
It alone does not establish the projection comparison or the
fixed-positive-noise assertion.

For the latter fix $\epsilon>0$, put $d_n=2n+1$, and use the
different maps $F_a(\eta)=(a\eta_X,\epsilon a\eta_z)$.
Their Jacobian is $\epsilon a^{d_n}$. The rescaled horizontal
fields and central field are

$$
 aF_a^*U_j=\partial_{\eta_{x_j}}
        -\frac{a\eta_{y_j}}{2\epsilon}\partial_{\eta_z},\qquad
 aF_a^*V_j=\partial_{\eta_{y_j}}
        +\frac{a\eta_{x_j}}{2\epsilon}\partial_{\eta_z},\qquad
 aF_a^*(\epsilon Z)=\partial_{\eta_z}.
\tag{10.18}
$$

Thus the fixed-noise tangent is the covariance-$2$ Euclidean heat
kernel in $d_n$ coordinates, with the stated density:

$$
 \epsilon a^{d_n}h_{n,\epsilon}(a^2t,F_a\eta)
   \longrightarrow (4\pi t)^{-d_n/2}e^{-|\eta|^2/(4t)}
\tag{10.19}
$$

uniformly on compact subsets of $(0,\infty)\times\mathbb R^{d_n}$.
This is the classical fixed-source heat tangent theorem, in the
full-rank case, of Colin de Verdière–Hillairet–Trélat,
[*Small-time asymptotics of hypoelliptic heat kernels near the
diagonal, nilpotentization and related results*, Theorem B,
(2.8)](https://doi.org/10.5802/ahl.93).
In coordinates $(X,z/\epsilon)$ the density is exactly
$\epsilon\,d\eta$, all weights are one, the drift is zero, and
the frame (10.18) converges to the coordinate frame. These facts
give the factor $\epsilon$ and the Gaussian in (10.19).

Choose a normalized compact smooth complex $u(\eta)$ supported
in a fixed compact annulus $A$ avoiding $0$, and define
$v_a(F_a\eta)=(\epsilon a^{d_n})^{-1/2}u(\eta)$.
The convergence (10.18) and the positive minimum in (10.19) on
$[1,2]\times A$ give, for small $a$,

$$
 \|v_a\|_2=1,\qquad T_{n,\epsilon}[v_a]\le C_\epsilon a^{-2},
 \qquad G_{n,\epsilon}(F_a\eta)
       \ge c\epsilon^{-1}a^{2-d_n}\quad(\eta\in A).
\tag{10.20}
$$

The last bound integrates only the times $[a^2,2a^2]$ as a lower
bound on the full positive Green field. Since $d_n-2=2n-1>2$
for $n\ge2$, (10.20) proves fixed-positive-noise full collapse.
For $n=2$ its negative scale is $a^{-3}$, whereas (10.17) has
negative scale $a^{-4}$; the kinetic scale is $a^{-2}$ in both cases.
The factor $a/\epsilon$ explains why this proof is not uniform
down to zero noise.

Finally keep $D$ fixed. Its Dirichlet operator has a positive
spectral gap: in the coordinates $(x_1,y_1,z+x_1y_1/2,\ldots)$,
$U_1=\partial_{x_1}$, the Jacobian is one, and zero extension to a
containing bounded $x_1$ interval gives the one-dimensional
Dirichlet Poincaré inequality. The sub-Markov bound for $0<t<1$
and the spectral-gap semigroup bound for $t\ge1$ give
$G^D_{n,\epsilon}\in L^1(D)$, finite and smooth off $0$.
Interior heat localization, Theorem 3.2 of the same primary source,
gives $h^D_{n,\epsilon}(t,0,p)-h_{n,\epsilon}(t,p)=O(t^N)$
on a fixed compact source neighbourhood for every $N$.
Its hypotheses hold here: the free realizations are selfadjoint
contractions, the density and fields coincide in the interior,
and the fields are smooth and bracket generating, also at zero
noise. At zero noise combine localization with exact contact heat
scaling; at positive fixed noise combine it with (10.19).
The same positive finite-time minima yield respectively
$G^D_{n,0}(\delta_a\eta)\ge ca^{-2n}$ and
$G^D_{n,\epsilon}(F_a\eta)\ge c\epsilon^{-1}a^{2-d_n}$
on $A$. The normalized tests in (10.17) or (10.20) eventually lie
in $C_c^\infty(D\setminus\{0\})$. They prove the second line of
(10.7) using the original field, without regenerating it on their
supports. Adding $s\|u\|_2^2$ for any finite $s$ cannot bound
these normalized values below. A negative shifted zero-trace
direction can also be multiplied by arbitrary real scalars, giving
the unnormalized response obstruction. $\square$

**Definition 10.3 (source correspondence and conditional scope).**
The joint relation in Theorem 10.2 uses the very same higher-contact
pole and heat law to define $G_{n,\epsilon}$, its actual retained
marginal $M_{n,\epsilon}$, and the failure of autonomy of $\pi$.
The retained reference form (10.6) is an analytic comparison on
$H^1$, not an asserted generator of the projected process.
For a full normalized state $u$, its interaction instead uses
$\int G_{n,\epsilon}(\xi,W)|u(\xi,W)|^2dW\,d\xi$;
disintegration weights the field by the state's conditional fibre
law, whereas (10.2) integrates against unweighted $dW$.
That infinite fibre measure is not a probability law. Consequently
the positive retained form does not determine the full interaction
or contradict (10.7).

The $n=1$ case recovers exactly the whole-group unit-source fields
and constants of §9. The actual native cylinder is still Definition
1.1's different global domain and raw source: in its local chart
$d\mu=m_0d\xi$, $m_0=(2r)^{-1}$, so its local unit-source
Green coefficient is $m_0^{-1}$ times the Lebesgue coefficient.
Its original killed field and traces remain those of §§1–5, and
Theorem 9.3 supplies the exact native positive interval
$0\le g\le m_0K$, with its finite shift and zero-noise critical
completion. A fixed positive-noise native form is semibounded
even above that interval; Theorem 5.1 excludes a common shift
down to arbitrarily small noise. Neither conclusion is replaced
by the higher-contact all-coupling collapse.

The oscillator columns, Folland gauge kernel, Hardy ingredients,
heat tangents and localization are literature-attested intermediate
results. Kombe's Hardy multiplier is
$|\nabla_HR_n|^2/R_n^2$, not the own-Green multiplier
$c_nR_n^{-2n}$. Bonnefont–Juillet,
[*Couplings in $L^p$ distance of two Brownian motions and their
Lévy area*, §§2.1,6](https://arxiv.org/html/1801.04109v2),
uses these contact fields with generator one half of the horizontal
sum of squares; its Brownian clock must be evaluated at $2t$ for
(10.1). Bureš–Siegl,
[*Hydrogen atom in space with a compactified extra dimension and
potential defined by Gauss' law*, §2](https://arxiv.org/html/1409.8530v1),
treats an elliptic four-dimensional inverse-square boundary, rather
than the fixed-positive-noise dimensions $2n+1\ge5$ here.
The prior rank-three carrier in continuation III, §§82–83, is
$H^1\times\mathbb R$ with a Brownian three-coordinate factor;
the hidden-circle quotient in
[Native observation quotient Green escape, §§2–3](FIB_NATIVE_OBSERVATION_QUOTIENT_GREEN_ESCAPE.md)
also has its own factor and measure. Neither supplies (10.3),
(10.11) or (10.13) for this retained contact coordinate.
The repository-derived content is their joint source-relative
comparison with (10.6) and (10.7), with no global priority claim.

Horizontal rank $2n$, topological dimension $2n+1$, contact
homogeneous dimension $2n+2$, the three retained coordinates and
the fixed-noise elliptic tangent dimension are distinct quantities.
This conditional analytic comparison supplies no native realization
of $H^n$ for $n>1$, no permission to discard hidden coordinates,
and no source-to-physical-space correspondence. It therefore
does not identify any of those dimensions with physical space,
linear state rank, response rank or a number of bits.

## 追加锚（本行以下为增补区）

## 11. Sharp central remainder and nonattainment

**Definition 11.1 (the fixed full-Green quotient).** Retain exactly
Definition 9.1's complex closure $\mathcal H_1$, fields $U,V,Z_H$,
Lebesgue measure and natural angular constant $K=2\pi\lambda_0$.
Write

$$
W[u]=\int_{\mathbb R^3}\mathcal G_1(\xi)|u(\xi)|^2\,d\xi,
\qquad Q[u]=\frac{\mathcal T_1[u]}{W[u]}\quad(0\ne u\in\mathcal H_1).
\tag{11.1}
$$

Here $\mathcal G_1=\int_0^\infty h_1(t,\cdot)\,dt$ is the
original-clock Lebesgue unit-source Green field of (9.2), with both
time endpoints retained. C, Definition 16.2, gives $0<W[u]<\infty$
for every nonzero $u\in\mathcal H_1$.

**Corollary 11.2 (optimal central coefficient and no extremizer).**
For every complex $u\in\mathcal H_1$, including zero and with no
angular symmetry assumption,

$$
\mathcal T_1[u]-K W[u]\ge\|Z_Hu\|_2^2.
\tag{11.2}
$$

The central coefficient one is optimal even on the compact smooth
core: for every real $c>1$ there is a nonzero
$u\in C_c^\infty(\mathbb R^3;\mathbb C)$ such that

$$
\mathcal T_1[u]-K W[u]<c\|Z_Hu\|_2^2.
\tag{11.3}
$$

Moreover,

$$
\mathcal T_1[u]>K W[u]\quad(0\ne u\in\mathcal H_1),
\qquad \inf_{0\ne u\in\mathcal H_1}Q[u]=K.
\tag{11.4}
$$

Thus the sharp quotient has no nonzero $\mathcal H_1$ extremizer.
Every normalized minimizing sequence $W[u_n]=1$,
$\mathcal T_1[u_n]\to K$ necessarily satisfies

$$
\|Z_Hu_n\|_2^2\le\mathcal T_1[u_n]-K\longrightarrow0.
\tag{11.5}
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
\tag{11.6}
$$

This proves weighted finiteness on the entire closure independently
of C, (15.8). Adding the closed central energy proves (11.2), also
for $u=0$.

To identify that central derivative, let $g$ be the $L^2$ limit of
$\partial_z u_j$. Integration by parts against any
$\eta\in C_c^\infty(\mathbb R^3;\mathbb C)$ yields

$$
\int g\,\overline\eta\,d\xi
 =\lim_j\int\partial_z u_j\,\overline\eta\,d\xi
 =-\lim_j\int u_j\,\overline{\partial_z\eta}\,d\xi
 =-\int u\,\overline{\partial_z\eta}\,d\xi.
\tag{11.7}
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
\tag{11.8}
$$

Given $c>1$, choose $s^2=(c-1)B/[2(A+B)]>0$.
By (11.6), $W[u_s]$ is finite, and its nonnegativity implies

$$
\mathcal T_1[u_s]-K W[u_s]\le B+s^2 A
 \le B+\tfrac12(c-1)B<cB.
\tag{11.9}
$$

This proves (11.3). No homogeneity, pole regularity or asymptotic
formula for $\mathcal G_1$ is used; its clock, source and full-time
integral are unchanged.

For nonzero $u$, (11.2) and the zero-kernel argument give the strict
inequality in (11.4). The positive denominator supplied by C,
Definition 16.2, permits division. Theorem 9.3, using C, Theorem
16.3's annular upper bound, already supplies the infimum $K$.
Consequently it is attained by no nonzero member of $\mathcal H_1$.
Finally (11.2) gives (11.5) directly. $\square$

The Fatou passage, distributional integration by parts, Young's
inequality and approximate-identity convergence used in this proof
are classical measure and convolution arguments; see G. B. Folland,
*Real Analysis*, second edition, Chapters 2 and 8. The dilation
identities (11.8) use only the fields of Definition 9.1. The
source-specific optimal-coefficient and nonattainment conclusions
are repo-derived consequences of (9.21), Theorem 9.3 and the positive
Green denominator in C, Definition 16.2; they assert no historical
priority. The vanishing in (11.5) is only a necessary central-energy
condition, with no profile convergence or compactness conclusion.
All statements concern the whole-group $\mathcal H_1$ closure;
they give no slab extremizer statement, zero-noise completed-domain
identification, physical realization or additional response rank law.

## 追加锚（本行以下为增补区）

## 12. Strict retained zero-noise gap for every higher-contact rank

**Definition 12.1 (the unchanged retained quotient and angular weight).**
Fix an arbitrary integer $n\ge2$ and retain Definition 10.1's parent
$H^n=\mathbb R^{2n}\times\mathbb R$, raw Lebesgue density, identity
unit pole and horizontal covariance-$2$ clock. In particular,

$$
\begin{aligned}
U_j&=\partial_{x_j}-\tfrac{y_j}{2}\partial_z,&
V_j&=\partial_{y_j}+\tfrac{x_j}{2}\partial_z,\\
L_{n,0}&=-\sum_{j=1}^n(U_j^2+V_j^2),&
G_{n,0}&=\int_0^\infty e^{-tL_{n,0}}\delta_0\,dt,\\
M_{n,0}(X_1,z)&=\int_{\mathbb R^{2n-2}}
                    G_{n,0}(X_1,W,z)\,dW,&X_1&=(x,y).
\end{aligned}
\tag{12.1}
$$

Both time endpoints and the entire unweighted fibre are retained.
Thus $M_{n,0}$ is exactly (10.2), with coefficient (10.5), rather
than a projected semigroup kernel or a state-conditioned interaction.
On retained $\mathbb R^3$ put $\rho=|X_1|$, $d\xi=dx\,dy\,dz$,
$U=\partial_x-(y/2)\partial_z$, $V=\partial_y+(x/2)\partial_z$ and
$\mathcal E_H[f]=\|Uf\|_2^2+\|Vf\|_2^2$. The domain remains

$$
\begin{aligned}
\mathcal H_0
 &=\overline{C_c^\infty(\mathbb R^3;\mathbb C)}^{\,
                  (\|f\|_2^2+\mathcal E_H[f])^{1/2}},\\
W_n[f]&=\int_{\mathbb R^3}M_{n,0}|f|^2\,d\xi,&
\Lambda_n&=\inf_{0\ne f\in\mathcal H_0}
                         \frac{\mathcal E_H[f]}{W_n[f]}.
\end{aligned}
\tag{12.2}
$$

The positivity and bound in Theorem 10.2 give $0<W_n[f]<\infty$
for nonzero $f\in\mathcal H_0$. This is the horizontal free closure,
with no central-derivative, angular-symmetry or trace requirement.
Use the polar coordinates of V, (10.9), in the retained variables:

$$
\begin{aligned}
R&=(\rho^4+16z^2)^{1/4},&
\rho^2&=R^2\cos a,&4z&=R^2\sin a,\\
J&=(-\pi/2,\pi/2),&c(a)&=\cos a,&
I_n&=\int_0^{\pi/2}\sin(t)^{n-2}\,dt,\\
q_n(a)&=\frac1{I_n}\int_0^1
          \frac{v^{n-2}}{\sqrt{1-v^2\sin^2a}}\,dv.
\end{aligned}
\tag{12.3}
$$

The natural complex angular domain and form are precisely those of
V, Definition 10.1 and Theorem 10.2:

$$
\begin{aligned}
\mathcal H_c&=\{b\in L^2(J;\mathbb C):b\in AC_{\rm loc}(J),\quad
                                  \sqrt c\,b'\in L^2(J)\},\\
A[b]&=\int_J\big(4c|b'|^2+c|b|^2\big)\,da,\\
\lambda_0&=\inf_{0\ne b\in\mathcal H_c}
                    \frac{A[b]}{\|b\|_2^2}>0,
\qquad K=2\pi\lambda_0,\\
\mu_n&=\inf_{0\ne b\in\mathcal H_c}
               \frac{A[b]}{\int_Jq_n|b|^2\,da}.
\end{aligned}
\tag{12.4}
$$

There are no imposed Dirichlet values at either endpoint. All
references to V here use the revision fixed in Definition 1.1.

**Theorem 12.2 (an attained angular bound and strict retained gap).**
For every integer $n\ge2$, the actual marginal has the exact angular
multiplier

$$
M_{n,0}(\rho,z)=\frac1{2\pi}R^{-2}q_n(a)\qquad(R>0).
\tag{12.5}
$$

Here $q_n$ extends continuously to $\overline J$ and satisfies

$$
q_n(\pm\pi/2)=1,\qquad
0<q_n(0)=\frac1{(n-1)I_n}\le q_n(a)<1\quad(a\in J).
\tag{12.6}
$$

The infimum $\mu_n$ is finite and is attained by some
$b_n\in\mathcal H_c$ with $\int_Jq_n|b_n|^2\,da=1$.
It satisfies $\mu_n>\lambda_0$. On the entire original complex
retained domain,

$$
\begin{aligned}
\mathcal E_H[f]&\ge2\pi\mu_n W_n[f]
                       &&(f\in\mathcal H_0),\\
K&<2\pi\mu_n\le\Lambda_n<\infty.
\end{aligned}
\tag{12.7}
$$

Proof. Set $D_n=c_n\pi^{n-1}/\Gamma(n-1)$, where $c_n$ is
exactly (10.5). The classical beta integral and gamma duplication
formula give

$$
\begin{aligned}
I_n&=\frac{\sqrt\pi\,\Gamma((n-1)/2)}{2\Gamma(n/2)},\\
\Gamma(n-1)&=\frac{2^{n-2}}{\sqrt\pi}
                 \Gamma((n-1)/2)\Gamma(n/2),\\
2\pi D_n&=\frac{2^{n-1}\Gamma(n/2)^2}{\pi\Gamma(n-1)}
             =\frac1{I_n}.
\end{aligned}
\tag{12.8}
$$

In the actual fibre integral (10.5), put $s=R^2u$. Its numerator
and denominator scale respectively as $R^{2n-2}$ and $R^{2n}$,
so the remaining integral is

$$
M_{n,0}=D_nR^{-2}\int_0^\infty
        \frac{u^{n-2}}{((u+\cos a)^2+\sin^2a)^{n/2}}\,du.
\tag{12.9}
$$

For $\alpha=|a|>0$, substitute
$u=\sin\alpha\cot\theta-\cos\alpha
=\sin(\alpha-\theta)/\sin\theta$.
As $u$ increases from $0$ to infinity, $\theta$ decreases from
$\alpha$ to $0$; also
$|du|=\sin\alpha\,\sin^{-2}\theta\,d\theta$ and
$(u+\cos\alpha)^2+\sin^2\alpha
=\sin^2\alpha/\sin^2\theta$.
The powers of $\sin\theta$ cancel, giving

$$
\begin{aligned}
q_n(a)
 &=\frac{\int_0^\alpha\sin(t)^{n-2}\,dt}
          {I_n\sin(\alpha)^{n-1}}\\
 &=\frac1{I_n}\int_0^1
         \frac{v^{n-2}}{\sqrt{1-v^2\sin^2\alpha}}\,dv.
\end{aligned}
\tag{12.10}
$$

The last equality uses $t=\arcsin(v\sin\alpha)$. At $a=0$,
the integral in (12.9) is
$\int_0^\infty u^{n-2}(1+u)^{-n}\,du=B(n-1,1)=1/(n-1)$,
which agrees with (12.3). Equations (12.8)–(12.10) prove (12.5)
with the original unit-source coefficient, density and clock.

For all $a\in\overline J$, the integrand in (12.3) is dominated by
$v^{n-2}/\sqrt{1-v^2}$, whose integral is $I_n$.
Dominated convergence proves continuity and the endpoint values.
For $a\in J$ and $0<v<1$,
$\sqrt{1-v^2\sin^2a}>\sqrt{1-v^2}$, proving $q_n(a)<1$.
The denominator in (12.3) is at most one, proving the positive
lower bound in (12.6). In particular $1-q_n>0$ almost everywhere
on $J$, although there is no uniform pointwise loss up to its
endpoints. Pointwise strictness alone does not establish a strict
gap between infima.

To obtain that gap, use the closedness and compact embedding
$\mathcal H_c\hookrightarrow L^2(J)$ supplied by V, Theorem 10.2.
These properties and $A\ge\lambda_0\|\cdot\|_2^2$ extend to
complex functions by splitting real and imaginary parts.
A nonzero constant trial gives $\mu_n<\infty$. Normalize a
minimizing sequence $b_j$ by $\int_Jq_n|b_j|^2\,da=1$.
Its bounded $A[b_j]$ and $\lambda_0>0$ bound its closed-form
Hilbert norm. The classical direct method gives a subsequence
converging weakly in that form norm and, by compactness, strongly
in $L^2(J)$ to $b_n\in\mathcal H_c$.
Boundedness of $q_n$ preserves the weighted normalization.
Weak lower semicontinuity of $A$ and the definition of the infimum
then imply $A[b_n]=\mu_n$. Since $b_n\ne0$,

$$
\begin{aligned}
\mu_n=A[b_n]
 &\ge\lambda_0\|b_n\|_2^2\\
 &=\lambda_0\left(1+\int_J(1-q_n)|b_n|^2\,da\right)
 >\lambda_0.
\end{aligned}
\tag{12.11}
$$

This compact angular minimization is on the natural finite-energy
domain, without changing its endpoint conditions.

For the transfer, let $f\in C_c^\infty(\mathbb R^3\setminus\{0\};
\mathbb C)$ be arbitrary, put $\ell=\log R$, and write
$f=R^{-1}v(\ell,a,\theta)$, with
$X_1=R\sqrt{\cos a}(\cos\theta,\sin\theta)$.
The raw volume is $R^3dR\,da\,d\theta/4$.
V, (10.9)–(10.11), give the full complex identity

$$
\mathcal E_H[f]=\frac14\int_{\mathbb R\times J\times\mathbb T}
 \left\{c|v_\ell-v+\tan a\,v_\theta|^2
        +4c|v_a+\tfrac12v_\theta|^2\right\}
          \,d\ell\,da\,d\theta.
\tag{12.12}
$$

Use the unitary Fourier transform in $\ell$ and the unitary Fourier
series in $\theta$. For each $\sigma\in\mathbb R$ and
$m\in\mathbb Z$, write the transformed coefficient as
$e^{-ima/2}b_{\sigma,m}(a)$. The same identity, together with
(12.5) and Plancherel, yields

$$
\begin{aligned}
\mathcal E_H[f]
 &=\frac14\sum_{m\in\mathbb Z}\int_{\mathbb R}\int_J
 \left\{4c|b'_{\sigma,m}|^2
   +c\big(1+(\sigma+m\tan a)^2\big)|b_{\sigma,m}|^2\right\}
      \,da\,d\sigma,\\
W_n[f]
 &=\frac1{8\pi}\sum_{m\in\mathbb Z}\int_{\mathbb R}\int_J
                         q_n|b_{\sigma,m}|^2\,da\,d\sigma.
\end{aligned}
\tag{12.13}
$$

Every finite-energy admissible fibre lies in the original
$\mathcal H_c$, as in V. Dropping only the nonnegative extra
square bounds its angular energy below by
$A[b_{\sigma,m}]\ge\mu_n\int_Jq_n|b_{\sigma,m}|^2\,da$.
The factors $1/4$ and $1/(8\pi)$ in (12.13) give precisely
$\mathcal E_H[f]\ge2\pi\mu_nW_n[f]$.
Every integer angular mode and almost every real radial frequency
are included; no radial or real-valued restriction is imposed.
The polar chart omits only measure-zero axes. The supplied identity
is obtained by integration and form approximation there, with the
natural $\mathcal H_c$ endpoints, not extra boundary values.

To remove the puncture, for a fixed complex compact smooth $f$
choose a smooth cutoff $\chi_\delta$ that is zero on the Euclidean
ball of radius $\delta$ and one outside the ball of radius
$2\delta$, with gradient bounded by $C/\delta$.
On the compact support of $f$, the coefficients of $U,V$ are
bounded. The added squared horizontal derivative error in
$\chi_\delta f$ is therefore
$O(\delta^3\delta^{-2})=O(\delta)$.
The removed original derivative terms and the $L^2$ error tend
to zero. This is the pole-cutoff argument of §9, so
$\chi_\delta f\to f$ in the horizontal form norm.
Nonnegativity of $M_{n,0}$ and Fatou's lemma extend the inequality
to every $f\in C_c^\infty(\mathbb R^3;\mathbb C)$.
For arbitrary $f\in\mathcal H_0$, take its defining smooth core
sequence. Horizontal derivative convergence gives convergence of
$\mathcal E_H$; $L^2$ convergence supplies an almost-everywhere
convergent subsequence. Fatou once more gives (12.7) on the whole
closure, including zero, and also weighted finiteness there.
Positivity of the actual marginal off the pole gives $W_n[f]>0$
for nonzero $f$. Division and infimum prove
$\Lambda_n\ge2\pi\mu_n>K$. A nonzero compact smooth test supported
in an annulus has finite energy and finite positive denominator,
so $\Lambda_n<\infty$. The integer $n\ge2$ was arbitrary. $\square$

**Corollary 12.3 (the strengthened sufficient zero-noise interval).**
For every integer $n\ge2$, with precisely the source, density,
clock and full complex domain of Definition 12.1, put
$\delta_n=2\pi(\mu_n-\lambda_0)>0$. Then

$$
\begin{aligned}
\mathcal E_H[f]&\ge(K+\delta_n)W_n[f]
                                      &&(f\in\mathcal H_0),\\
\mathcal E_H[f]-gW_n[f]
 &\ge\left(1-\frac{g}{2\pi\mu_n}\right)\mathcal E_H[f]\ge0
                       &&(0\le g\le2\pi\mu_n).
\end{aligned}
\tag{12.14}
$$

Proof. Substitute $K+\delta_n=2\pi\mu_n$ in (12.7), then multiply
$W_n[f]\le\mathcal E_H[f]/(2\pi\mu_n)$ by $g\ge0$.
Thus the sufficient interval for the retained reference form in
(10.6), at zero noise and this fixed $n$, contains
$[0,2\pi\mu_n]$, which strictly extends $[0,K]$. $\square$

The source-specific angular multiplier, its weighted minimization
and the resulting sufficient retained interval are repo-derived
consequences of (10.5) and V's natural angular form and all-mode
identity. The gauge-kernel ingredients keep their Folland/Kombe
attribution from §10. The beta/gamma identities, Rellich compactness
used in V, Hilbert-space direct method, weak lower semicontinuity,
dominated convergence, Plancherel and Fatou are classical
intermediate inputs, not additional new theorems. For these
variational and integration principles see L. C. Evans,
*Partial Differential Equations*, second edition, Chapters 5 and 8,
and G. B. Folland, *Real Analysis*, second edition, Chapters 2, 6
and 8. No historical priority claim accompanies this derivation.

The bound (12.7) does not identify the exact value of $\Lambda_n$
or assert $\Lambda_n=2\pi\mu_n$. Angular attainment in (12.11)
is not a whole-space optimizer assertion. The positive margin is
$n$-dependent; no uniform gap in $n$, positive-noise improvement,
slab or trace conclusion, or critical completed-domain
identification follows here. Section 11's different full-Green
quotient has individual-test strictness and infimum $K$; it supplies
no strict-infimum premise for (12.7). The retained comparison
remains Definition 10.3's analytic reference form. It creates no
autonomous retained generator, probability law on the whole fibre,
state-conditioned interaction, native higher-contact realization
or physical-space or response-rank interpretation.

## 追加锚（本行以下为增补区）

## 13. The exact retained zero-noise constant and full-domain nonattainment

**Definition 13.1 (the original quotient and its transformed remainder).**
Fix an integer $n\ge2$ and retain exactly Definition 12.1: the same
$H^n$ identity unit pole, raw Lebesgue density, covariance-$2$
horizontal clock, complete unweighted same-source marginal $M_{n,0}$,
and original full complex horizontal closure $\mathcal H_0$.
Use its $J$, $c$, $q_n$, $\mathcal H_c$, $A$, $\mu_n$, $W_n$ and
$\Lambda_n$, and write

$$
\begin{aligned}
q_*&=\frac1{(n-1)I_n}>0,&
Q_n[b]&=\int_Jq_n|b|^2\,da,&
C[b]&=\int_Jc|b|^2\,da,&
\lambda_n&=2\pi\mu_n.
\end{aligned}
\tag{13.1}
$$

Theorem 12.2 supplies $q_*\le q_n\le1$, the attained natural
angular infimum, and $\mathcal E_H\ge\lambda_nW_n$ on
$\mathcal H_0$. For a measurable $f$ use the same polar coordinates
as (12.12), set $\ell=\log R$, and put $v_f=Rf$. The raw
nonnegative-integral change of variables gives

$$
W_n[f]=\frac1{8\pi}
 \int_{\mathbb R\times J\times\mathbb T}q_n(a)|v_f|^2
                  \,d\ell\,da\,d\theta.
\tag{13.2}
$$

For $f\in\mathcal H_0$, finiteness of $W_n[f]$ and $q_*>0$
therefore give $v_f\in L^2(d\ell\,da\,d\theta)$.
Take the unitary Fourier transform in $\ell$ and unitary Fourier
series in $\theta$, and write the transformed coefficient as
$e^{-ima/2}b_{f,\sigma,m}(a)$, for $m\in\mathbb Z$ and
$\sigma\in\mathbb R$. Define the initially extended nonnegative
quantity

$$
B_n[f]=\sum_{m\in\mathbb Z}\int_{\mathbb R}\int_J
 c(a)\bigl(\sigma+m\tan a\bigr)^2
              |b_{f,\sigma,m}(a)|^2\,da\,d\sigma.
\tag{13.3}
$$

These transforms concern all angular modes of the original state;
no symmetry condition is imposed on $\mathcal H_0$.

**Theorem 13.2 (sharp constant, full-domain remainder and nonattainment).**
For every integer $n\ge2$, with precisely Definition 13.1's source
and domains,

$$
\begin{aligned}
\Lambda_n&=2\pi\mu_n,\\
\mathcal E_H[f]-2\pi\mu_nW_n[f]&\ge\frac14B_n[f]\ge0
                                  &&(f\in\mathcal H_0),\\
B_n[f]=0&\quad\Longleftrightarrow\quad f=0
                                  &&(f\in\mathcal H_0).
\end{aligned}
\tag{13.4}
$$

In particular $B_n[f]$ is finite on the original domain, and every
nonzero complex $f\in\mathcal H_0$ satisfies

$$
\mathcal E_H[f]>2\pi\mu_nW_n[f].
\tag{13.5}
$$

Thus the exact quotient has no nonzero original-domain extremizer,
although the natural angular infimum is attained.

**Proof.** Fix $n$. The lower bound
$\Lambda_n\ge2\pi\mu_n$ is already Theorem 12.2. To construct
legal upper trials, first approximate its angular minimizer in the
natural form norm, rather than impose boundary values on it.
Normalize a minimizer by $Q_n[b]=1$. The Sobolev modulus chain
rule on compact subintervals, with the weighted derivative integral,
gives $|b|\in\mathcal H_c$ and $A[|b|]\le A[b]$. The variational
infimum makes $|b|$ another minimizer, so take $b\ge0$ real.
The bounded value truncations $b_N=\min(b,N)$ converge to $b$
in $L^2(J)$ and in the seminorm $\|\sqrt c\,b'\|_2$, by
dominated convergence for the function and derivative tails.

For each fixed bounded truncation cut off its two endpoints
logarithmically. If $d$ denotes distance to either endpoint and
$0<\varepsilon<1/4$, use

$$
\eta_\varepsilon(d)=
\begin{cases}
0,&d\le\varepsilon^2,\\
\displaystyle\frac{\log(d/\varepsilon^2)}{\log(1/\varepsilon)},
                    &\varepsilon^2<d<\varepsilon,\\
1,&d\ge\varepsilon,
\end{cases}
\tag{13.6}
$$

and take the product of the two endpoint cutoffs. Near either
endpoint $c=\sin d\le d$, so its derivative cost satisfies

$$
\int c\,|\eta_\varepsilon'|^2\,da
 \le\frac1{\log(1/\varepsilon)^2}
                 \int_{\varepsilon^2}^{\varepsilon}\frac{dd}{d}
 =\frac1{\log(1/\varepsilon)}\longrightarrow0.
\tag{13.7}
$$

The bound on $b_N$ controls the added term $b_N\eta_\varepsilon'$.
Integrability of $c|b_N'|^2$ controls the removed derivative tail,
and dominated convergence controls the $L^2$ error. The product
therefore converges to $b_N$ in the natural form norm. On its
remaining compact support, $c$ is bounded below by a positive
number, so ordinary interior $H^1$ mollification gives real
compact smooth approximations. A diagonal choice yields nonzero
$b_j\in C_c^\infty(J;\mathbb R)$ with

$$
Q_n[b_j]\longrightarrow1,\qquad A[b_j]\longrightarrow\mu_n.
\tag{13.8}
$$

Boundedness of $q_n$ ensures the first convergence. This argument
uses the original natural finite-energy endpoints; it introduces
no Dirichlet trace requirement.

Choose a nonzero real $\chi\in C_c^\infty(\mathbb R)$ and, for
$L>0$, define the actual Cartesian trial

$$
f_{j,L}(x,y,z)=R^{-1}b_j(a)\chi(\log R/L).
\tag{13.9}
$$

Each trial has compact annular radial support away from the pole.
Its angular support is separated from the two central axes, so
extension by zero there is smooth. Thus
$f_{j,L}\in C_c^\infty(\mathbb R^3\setminus\{0\})
\subset\mathcal H_0$. In particular its original $L^2$ condition
holds: the raw Jacobian gives

$$
\|f_{j,L}\|_2^2=\frac\pi2\|b_j\|_2^2
              \int_{\mathbb R}e^{2\ell}|\chi(\ell/L)|^2\,d\ell
 <\infty.
\tag{13.10}
$$

No uniform bound on these $L^2$ norms is needed for the quotient.
Using (12.12), the exact multiplier (12.5), and
$\int\chi\chi'=0$, one obtains

$$
\begin{aligned}
\mathcal E_H[f_{j,L}]
 &=\frac\pi2\left(L\|\chi\|_2^2A[b_j]
                  +L^{-1}\|\chi'\|_2^2C[b_j]\right),\\
W_n[f_{j,L}]&=\frac14L\|\chi\|_2^2Q_n[b_j],\\
\frac{\mathcal E_H[f_{j,L}]}{W_n[f_{j,L}]}
 &=2\pi\left(\frac{A[b_j]}{Q_n[b_j]}
       +\frac{C[b_j]}{Q_n[b_j]}
                   \frac{\|\chi'\|_2^2}{L^2\|\chi\|_2^2}\right).
\end{aligned}
\tag{13.11}
$$

Since $C[b_j]/Q_n[b_j]\le1/q_*$, take $L=j$ and use (13.8).
The quotient tends to $2\pi\mu_n$, proving the matching upper
bound and hence the first line of (13.4). The symmetric functions
here are only upper trials, not a restriction on the lower-bound
domain.

For the remainder, take an arbitrary complex punctured compact
smooth $f$. The full all-mode identity (12.13) gives

$$
\begin{aligned}
\mathcal E_H[f]-\lambda_nW_n[f]
 &=\frac14\sum_{m\in\mathbb Z}\int_{\mathbb R}
       \left(A[b_{f,\sigma,m}]-\mu_nQ_n[b_{f,\sigma,m}]\right)
                      \,d\sigma+\frac14B_n[f]\\
 &\ge\frac14B_n[f].
\end{aligned}
\tag{13.12}
$$

Every admissible fibre lies in the supplied natural $\mathcal H_c$,
so each angular difference is nonnegative. This uses all integer
angular modes and almost every real radial frequency.

Now let $f\in\mathcal H_0$ be arbitrary. The pole cutoff in the
proof of Theorem 12.2 makes the punctured smooth core form dense:
for a fixed compact smooth function its added squared horizontal
derivative cost is $O(\delta^3\delta^{-2})=O(\delta)$, and the
removed original derivative and $L^2$ tails tend to zero.
A diagonal choice therefore supplies punctured smooth $f_k\to f$
in the original horizontal form norm. Apply Theorem 12.2 to the
actual difference $f_k-f\in\mathcal H_0$:

$$
W_n[f_k-f]\le\lambda_n^{-1}\mathcal E_H[f_k-f]
                         \longrightarrow0.
\tag{13.13}
$$

Thus $W_n[f_k]\to W_n[f]$, and the form convergence also gives
$\mathcal E_H[f_k]\to\mathcal E_H[f]$. Equation (13.2), with
$q_n\ge q_*$, gives

$$
\|v_{f_k}-v_f\|_2^2\le\frac{8\pi}{q_*}W_n[f_k-f]
                         \longrightarrow0.
\tag{13.14}
$$

The unitary Fourier maps and the unit-modulus angular gauge
therefore give strong $L^2$ convergence of $b_{f_k,\sigma,m}$
to $b_{f,\sigma,m}$ in counting measure on $\mathbb Z$ times
Lebesgue measure on $\mathbb R\times J$. Choose an almost-everywhere
convergent subsequence and relabel it. Fatou and (13.12) imply

$$
\begin{aligned}
B_n[f]&\le\liminf_k B_n[f_k]
       \le\limsup_k B_n[f_k]\\
 &\le4\lim_k\left(\mathcal E_H[f_k]-\lambda_nW_n[f_k]\right)
  =4\left(\mathcal E_H[f]-\lambda_nW_n[f]\right).
\end{aligned}
\tag{13.15}
$$

This proves the remainder and its finiteness on every original
complex $\mathcal H_0$ state. It requires no unproved equality
between closed direct-integral domains.

Finally, for every fixed $m\in\mathbb Z$ and $a\in J$, $c(a)>0$
and the multiplier in (13.3) vanishes only at the singleton
$\sigma=-m\tan a$. Tonelli makes its zero set null in the
$(a,\sigma)$ product measure; the countable union over $m$
is still null in the stated counting-product measure.
Consequently $B_n[f]=0$ forces every transformed coefficient
to vanish almost everywhere. Plancherel gives $v_f=0$, and the
coordinate change gives $f=0$ off the null axes and pole, hence
$f=0$ in the original $L^2$ space. The converse is immediate.
Equation (13.15) proves (13.5), completing the proof. $\square$

**Corollary 13.3 (the exact nonnegative retained coupling interval).**
For each integer $n\ge2$ define, on exactly $\mathcal H_0$,

$$
\mathfrak q_{n,g}[f]=\mathcal E_H[f]-gW_n[f],\qquad g\ge0.
\tag{13.16}
$$

Then $\mathfrak q_{n,g}\ge0$ on its entire original domain if and
only if $0\le g\le2\pi\mu_n$. At $g=2\pi\mu_n$ it is strictly
positive on every nonzero original-domain state. For every
$g>2\pi\mu_n$ there is a nonzero compact smooth state with
$\mathfrak q_{n,g}[f]<0$.

**Proof.** Nonnegativity throughout the stated interval follows
from (12.14), and endpoint strictness is (13.5). For larger $g$,
the actual trials $f_{j,j}$ in (13.9) have positive denominator
and quotient tending to $2\pi\mu_n<g$. A sufficiently large
$j$ is therefore a compact smooth negative direction. $\square$

**Definition 13.4 (mathematical attribution and scope).**
The exact multiplier, natural angular minimization, lower bound
and all-mode core identity are the supplies of §12, with V's
pinned natural angular form and polar identities. The passage
from these supplies to actual sharp trials, full-domain strictness
and the exact retained coupling interval is repo-derived.
Value truncation, the modulus chain rule, logarithmic endpoint
cutoffs, interior mollification, unitary Fourier theory and Fatou
are classical intermediate principles; see L. C. Evans,
*Partial Differential Equations*, second edition, Chapters 5 and 8,
and G. B. Folland, *Real Analysis*, second edition, Chapters 2, 6
and 8. These general principles are not new standalone results.
The Folland fundamental solution and the Hardy literature retain
the limited attribution in §10. In particular Kombe,
[*Sharp Hardy type inequalities on the Carnot Group*, Theorem 3.1](https://arxiv.org/html/math/0501522v1),
uses the gradient-weighted multiplier rather than this actual
unweighted marginal. D'Arca–Fanelli–Franceschi–Prandi,
[Theorem 1.2](https://arxiv.org/html/2603.04086v1), supplies the
lower-bound comparison identified in V, rather than the present
exact $q_n$ quotient. No exhaustive literature priority is asserted.

The coupling form here remains Definition 10.3's retained analytic
reference form, not an autonomous projected generator or a
state-conditioned interaction. Angular attainment and actual
annular sharpness do not yield a whole-space optimizer; (13.5)
excludes one in the original domain. No uniform-in-$n$ margin,
positive-noise sharpness, attractive completed-domain identification,
native source-to-state realization or physical dimension conclusion
is supplied. The parent self-field collapse and nonautonomous
retention statements of §10 are unchanged.

## 追加锚（本行以下为增补区）

## 14. The exact retained constant at every positive central noise

**Definition 14.1 (the original positive-noise retained quotient).**
Fix an integer $n\ge2$ and a real $\epsilon>0$. Retain exactly
Definition 10.1's $H^n$ identity unit source, raw Lebesgue density,
covariance-$2$ horizontal clock, independent central covariance
$2\epsilon^2$, and complete unweighted marginal $M_{n,\epsilon}$.
On the retained $\mathbb R^3$ use the same fields $U,V,Z$ and set

$$
\begin{aligned}
T_\epsilon[f]&=\mathcal E_H[f]+\epsilon^2\|Zf\|_2^2,\\
\mathcal H_\epsilon
 &=\overline{C_c^\infty(\mathbb R^3;\mathbb C)}^
                   {(\|f\|_2^2+T_\epsilon[f])^{1/2}},\\
W_{n,\epsilon}[f]&=\int_{\mathbb R^3}M_{n,\epsilon}|f|^2\,d\xi,\\
\Lambda_{n,\epsilon}
 &=\inf_{0\ne f\in\mathcal H_\epsilon}
                         \frac{T_\epsilon[f]}{W_{n,\epsilon}[f]},\\
\lambda_n&=2\pi\mu_n.
\end{aligned}
\tag{14.1}
$$

Here $\mu_n$ is precisely Definition 12.1's natural angular
infimum, with the same $q_n$ and no imposed endpoint trace.
Theorem 10.2 supplies positive finite denominators for nonzero
states in this original free domain, which is contained in
$\mathcal H_0$. No symmetry condition is imposed.

**Theorem 14.2 (positive-noise sharpness and strictness on the full domain).**
For every integer $n\ge2$ and every real $\epsilon>0$, with
exactly Definition 14.1's objects,

$$
\begin{aligned}
\Lambda_{n,\epsilon}&=2\pi\mu_n,\\
T_\epsilon[f]-2\pi\mu_nW_{n,\epsilon}[f]
 &\ge\epsilon^2\|Zf\|_2^2
 &&(f\in\mathcal H_\epsilon),\\
T_\epsilon[f]&>2\pi\mu_nW_{n,\epsilon}[f]
 &&(0\ne f\in\mathcal H_\epsilon).
\end{aligned}
\tag{14.2}
$$

In particular the sharp quotient has no nonzero extremizer in
the original full complex free domain.

**Proof.** Fix $n$ and $\epsilon$. First let
$f\in C_c^\infty(\mathbb R^3;\mathbb C)$ be arbitrary.
Use the rotation norm and central Fourier modulus from
(9.11)–(9.17):

$$
\begin{aligned}
w(\rho,z)&=\left(\frac1{2\pi}\int_0^{2\pi}
                         |f(\rho,\theta,z)|^2\,d\theta\right)^{1/2},\\
F(\rho,k)&=\int_{\mathbb R}e^{-ikz}w(\rho,z)\,dz,
&\psi(\rho,k)&=|F(\rho,k)|,\\
v(\rho,z)&=\frac1{2\pi}\int_{\mathbb R}e^{ikz}\psi(\rho,k)\,dk.
\end{aligned}
\tag{14.3}
$$

The inverse is initially in $L^2$. Those supplied norm-chain-rule
and Plancherel arguments give

$$
\begin{aligned}
W_{n,\epsilon}[w]&=W_{n,\epsilon}[f],\\
v\in\mathcal H_1\subset\mathcal H_0,
\qquad \mathcal E_H[v]&\le\mathcal E_H[w]
                                  \le\mathcal E_H[f].
\end{aligned}
\tag{14.4}
$$

The first equality uses rotation invariance of the actual marginal.
The construction is an auxiliary transformation of an unrestricted
complex input. In particular the rotation norm does not discard
the input's magnetic angular energy: with
$D=\rho^{-1}\partial_\theta+(\rho/2)\partial_z$,
periodicity gives
$(\rho/2)ww_z=\operatorname{Re}(2\pi)^{-1}
\int\overline f\,Df\,d\theta$, and Cauchy–Schwarz bounds this
part by the original $|Df|^2$ energy. The norm chain rule controls
the radial derivative. The Fourier modulus contracts the radial
derivative and preserves the $\rho^2k^2/4$ term. Membership of $v$
in the original closure follows by cutting off its central tails
and mollifying in Euclidean $H^1$ on a fixed bounded horizontal
support, where the field coefficients are bounded independently
of $z$, exactly as in (9.16).

Write $P_{n,\eta}(t,\rho,k)=\widehat m_{n,\eta}(t,\rho,k)$.
Keep the higher-contact factor in (10.3), rather than compare
to the native rank-one field. For every $t>0$,

$$
\begin{aligned}
P_{n,\epsilon}(t,\rho,k)
 &=e^{-\epsilon^2tk^2}P_{n,0}(t,\rho,k),\\
P_{n,0}(t,\rho,k)
 &=\frac{|k|}{4\pi\sinh(|k|t)}
       e^{-|k|\rho^2\coth(|k|t)/4}
                           \operatorname{sech}(|k|t)^{n-1},\\
0&\le P_{n,\epsilon}(t,\rho,k)\le P_{n,0}(t,\rho,k).
\end{aligned}
\tag{14.5}
$$

At $k=0$ the second line denotes its continuous value
$B(t,\rho)=(4\pi t)^{-1}e^{-\rho^2/(4t)}$. Each column is real
and even, and its modulus is at most $B(t,\rho)$, the central
mass of the corresponding fixed-time density.

For almost every $\rho>0$, (9.17) gives $F(\rho,\cdot)\in L^1$.
The bound by $B(t,\rho)$ therefore makes all the following double
integrals absolutely convergent, with absolute value bounded by
$B(t,\rho)\|F(\rho,\cdot)\|_1^2/(2\pi)^2$. The same fixed-time
Fourier inversion as (9.18)–(9.19) gives

$$
\begin{aligned}
\int_{\mathbb R}m_{n,\epsilon}(t,\rho,z)|w|^2\,dz
 &=\frac1{(2\pi)^2}\iint
       P_{n,\epsilon}(t,\rho,k-\ell)
           F(\rho,k)\overline{F(\rho,\ell)}\,dk\,d\ell\\
 &\le\frac1{(2\pi)^2}\iint
       P_{n,0}(t,\rho,k-\ell)
                   \psi(\rho,k)\psi(\rho,\ell)\,dk\,d\ell\\
 &=\int_{\mathbb R}m_{n,0}(t,\rho,z)|v|^2\,dz.
\end{aligned}
\tag{14.6}
$$

The inequality takes the modulus of the first, real nonnegative
pairing and then uses (14.5). Integrate the physical nonnegative
pairings first in $2\pi\rho\,d\rho$ and then over all
$0<t<\infty$. Tonelli and the complete-time identity (10.4) give

$$
\lambda_nW_{n,\epsilon}[f]
 \le\lambda_nW_{n,0}[v]
 \le\mathcal E_H[v]\le\mathcal E_H[f].
\tag{14.7}
$$

The middle inequality is the supplied zero-noise inequality of
Theorems 12.2 and 13.2. Its finite right side also controls the
entire time integral. No signed infinite-time Fourier integral,
pointwise Green ordering, or removal of a time endpoint is used.

For arbitrary $f\in\mathcal H_\epsilon$ take its defining compact
smooth core sequence. It converges in $L^2$ and in horizontal
derivative norms, and a subsequence converges almost everywhere.
Fatou applied to the nonnegative actual marginal extends (14.7)
to $f$. Adding $\epsilon^2\|Zf\|_2^2$ proves the second line of
(14.2), and hence $\Lambda_{n,\epsilon}\ge\lambda_n$.

For the opposite inequality reuse the actual nonzero compact smooth
annular tests $g_j=f_{j,j}$ of (13.9)–(13.11). They satisfy

$$
\frac{\mathcal E_H[g_j]}{W_{n,0}[g_j]}\longrightarrow\lambda_n,
\qquad \|Zg_j\|_2<\infty.
\tag{14.8}
$$

In particular these are Cartesian functions supported away from
the pole, with the original natural angular endpoints handled by
the approximations (13.6)–(13.8).

For any fixed such test $g$ and any $a>0$ put
$D_ag(X_1,z)=a^{-1}g(X_1/a,z/a^2)$. The retained Jacobian is
$a^4$. The exact complete-field scaling following (10.12) and the
original field identities give

$$
\begin{aligned}
M_{n,\epsilon}(aX_1,a^2z)&=a^{-2}M_{n,\epsilon/a}(X_1,z),\\
\|D_ag\|_2^2&=a^2\|g\|_2^2,
&\mathcal E_H[D_ag]&=\mathcal E_H[g],\\
\|ZD_ag\|_2^2&=a^{-2}\|Zg\|_2^2,
&W_{n,\epsilon}[D_ag]&=W_{n,\epsilon/a}[g].
\end{aligned}
\tag{14.9}
$$

The field scaling retains the complete parent time integral and
the whole omitted fibre: their scaling factors are respectively
$a^2$ and $a^{2n-2}$, against the parent heat-density factor
$a^{-(2n+2)}$. Every finite-$a$ test remains in the original
compact smooth core for the fixed original $\epsilon$.

The off-pole locally uniform limit supplied by (10.9)–(10.10)
and the large-time bound in Theorem 10.2 gives, on the fixed
compact support of $g$,
$W_{n,\epsilon/a}[g]\to W_{n,0}[g]>0$. Thus

$$
\frac{T_\epsilon[D_ag]}{W_{n,\epsilon}[D_ag]}
 =\frac{\mathcal E_H[g]+\epsilon^2a^{-2}\|Zg\|_2^2}
              {W_{n,\epsilon/a}[g]}
 \longrightarrow\frac{\mathcal E_H[g]}{W_{n,0}[g]}
 \qquad(a\to\infty).
\tag{14.10}
$$

Apply this limit separately to each $g_j$. It gives
$\Lambda_{n,\epsilon}\le\mathcal E_H[g_j]/W_{n,0}[g_j]$
for every $j$, and then (14.8) proves the matching upper bound.
Equivalently, choose a finite $a_j$ for each $j\ge2$ such that

$$
\left|\frac{W_{n,\epsilon/a_j}[g_j]}{W_{n,0}[g_j]}-1\right|
 \le\frac1j,
\qquad
\frac{\epsilon^2a_j^{-2}\|Zg_j\|_2^2}{W_{n,0}[g_j]}
 \le\frac1j.
\tag{14.11}
$$

The actual tests $D_{a_j}g_j$ then have quotient at most
$(\mathcal E_H[g_j]/W_{n,0}[g_j]+1/j)/(1-1/j)$, which tends
to $\lambda_n$. No estimate uniform in $j$, $n$ or $\epsilon$
is required, and the original tested Green field always has the
fixed noise $\epsilon$.

Finally $Zf=0$ in distributions for an $L^2(\mathbb R^3)$ state
forces $f=0$: its partial Fourier transform is supported on the
null set $k=0$, so vanishes in $L^2$. The positive central
remainder in (14.2) is therefore strictly positive for every
nonzero $f\in\mathcal H_\epsilon$. This proves the final line
and nonattainment. $\square$

**Corollary 14.3 (the exact positive-noise nonnegative coupling range).**
For every fixed $n\ge2$, $\epsilon>0$ and $g\ge0$, on exactly
$\mathcal H_\epsilon$ define

$$
\mathfrak q_{n,\epsilon,g}[f]
        =T_\epsilon[f]-gW_{n,\epsilon}[f].
\tag{14.12}
$$

This form is nonnegative on its entire original domain if and
only if $0\le g\le2\pi\mu_n$. Throughout this interval,

$$
\mathfrak q_{n,\epsilon,g}[f]
 \ge\left(1-\frac{g}{2\pi\mu_n}\right)T_\epsilon[f],
\tag{14.13}
$$

and at the endpoint it is strictly positive on every nonzero
original-domain state. For each $g>2\pi\mu_n$ there is a nonzero
compact smooth state making (14.12) negative.

**Proof.** Theorem 14.2 gives
$W_{n,\epsilon}[f]\le T_\epsilon[f]/\lambda_n$ and endpoint
strictness. For $g>\lambda_n$, one of the actual trials in
(14.11) has quotient below $g$, so its form value is negative.
$\square$

**Definition 14.4 (correspondence, attribution and scope).**
The same higher-contact source generates both the original full
field and its unweighted retained marginal. Theorem 10.2 supplies
their fixed-time columns, complete-time estimates and exact scaling;
Theorem 13.2 supplies the natural angular constant and actual
annular sharp tests. The rotation-norm and Fourier-modulus
constructions, their original-domain membership, and the
absolutely convergent fixed-time pairing are reused from §9.
The source-relative additional composition keeps the rank-$n$
factor in the noise comparison and applies the supplied sharp tests
to the fixed positive-noise marginal by outward dilation.

The oscillator formula, Plancherel, Sobolev norm and modulus chain
rules, cutoff approximation, Fubini, Tonelli and Fatou are classical
intermediate principles, with the attributions in §§9–10 and 13.
In particular Krötz–Thangavelu–Xu,
[*The heat kernel transform for the Heisenberg group*, §2.2,
(2.2.1) and §4.1, (4.1.2)](https://arxiv.org/html/math/0401243v2),
supplies classical heat columns rather than this exact retained
quotient. The different multipliers and lower-bound comparisons
of Kombe and D'Arca–Fanelli–Franceschi–Prandi retain the limited
attribution in Definitions 9.4 and 13.4. The composition here is
repo-derived; no exhaustive literature priority is asserted.

The coupling form remains Definition 10.3's retained analytic
reference form. Its exact nonnegative interval does not identify
a critical attractive completion, classify shifted semiboundedness
outside the interval, or turn the nonautonomous retained densities
into a projected semigroup. The result supplies no estimate uniform
in rank or noise, native source-to-state realization, physical
forcing or physical dimension conclusion. The parent self-field
collapse and source-retention obstructions of §10 are unchanged.

## 追加锚（本行以下为增补区）

## 15. The supercritical retained operator and its infinite negative spectrum

**Definition 15.1 (the original retained form and its realization).**
Fix an integer $n\ge2$, $\epsilon>0$, and
$g>\lambda_n=2\pi\mu_n$, with exactly the source and fields of
Definition 10.1 and the angular constant of Definition 13.1. Write
$M=M_{n,\epsilon}$ for the actual complete unweighted marginal,
$W=W_{n,\epsilon}$ and $T=T_\epsilon$ as in Definition 14.1.
All norms and scalar products use complex $L^2(\mathbb R^3,d\xi)$
with raw $d\xi=dx\,dy\,dz$. The form in question is

$$
 q[f]=T[f]-gW[f],\qquad D(q)=\mathcal H_\epsilon .
 \tag{15.1}
$$

Thus its domain is the original full complex free closure. A
Friedrichs realization below means the self-adjoint operator
associated with this form after closedness and lower
semiboundedness have been established. It does not mean the
higher-contact parent attractive operator of (10.7).

**Theorem 15.2 (closed supercritical form and complete negative spectrum).**
For every set of parameters in Definition 15.1, the form (15.1)
is densely defined, closed and lower semibounded on exactly
$\mathcal H_\epsilon$, and its compact smooth core remains a form
core. Its associated Friedrichs operator $A_{n,\epsilon,g}$ satisfies

$$
 \sigma_{\mathrm{ess}}(A_{n,\epsilon,g})=[0,\infty).
 \tag{15.2}
$$

The negative spectrum consists of infinitely many isolated
eigenvalues of finite multiplicity. Listed with multiplicity, they
can be arranged as

$$
 -\infty<E_1\le E_2\le\cdots<0,\qquad E_j\longrightarrow0.
 \tag{15.3}
$$

There is no other accumulation point of the negative spectrum.
The constants needed for lower boundedness are allowed to depend
on $n,\epsilon,g$.

**Proof.** We first check the singularity and tail of the actual
potential. The nonnegative central convolution (10.4), the Gaussian
supremum and the zero Fourier mode (10.3) give, for $t>0$,

$$
\begin{aligned}
 m_{n,\epsilon}(t,\rho,z)
 &\le \|\varphi_{\epsilon,t}\|_\infty
                \int_{\mathbb R}m_{n,0}(t,\rho,s)\,ds\\
 &=(4\pi)^{-3/2}\epsilon^{-1}t^{-3/2}
                 e^{-\rho^2/(4t)}.
\end{aligned}
\tag{15.4}
$$

Integrate this nonnegative estimate over the whole time interval.
For $\rho>0$,

$$
 \int_0^\infty t^{-3/2}e^{-\rho^2/(4t)}dt
       =\frac{2\sqrt\pi}{\rho},
 \qquad
 0<M(\rho,z)\le\frac1{4\pi\epsilon\rho}.
 \tag{15.5}
$$

This estimate does not infer pointwise order from Fourier-column
order. On every bounded set, cylindrical integration of
$\rho^{-p}$ shows that $M\in L^p_{\mathrm{loc}}$ for
$1\le p<2$. In particular we can fix $p=7/4>3/2$.

For the tail set
$R(\xi)=(\rho^4+16z^2)^{1/4}$,
$\delta_a(x,y,z)=(ax,ay,a^2z)$ and $\Sigma=\{R=1\}$.
The uniform off-pole small-time bounds (10.9)--(10.10) and their
large-time $C_nt^{-2}$ bound imply

$$
 C_{n,\epsilon}:=
 \sup_{\substack{0\le\eta\le\epsilon\\\omega\in\Sigma}}
          M_{n,\eta}(\omega)<\infty .
 \tag{15.6}
$$

Here $\Sigma$ is compact and avoids the pole, and the cited
bounds dominate the complete time integral uniformly on the
displayed parameter interval. The exact scaling (14.9), with
$a=R(\xi)\ge1$, now gives

$$
 M(\xi)=a^{-2}M_{n,\epsilon/a}(\delta_{1/a}\xi)
       \le C_{n,\epsilon}R(\xi)^{-2}.
 \tag{15.7}
$$

Together with off-pole continuity, this proves boundedness outside
any fixed source neighbourhood and uniform decay to zero at
spatial infinity.

We next verify the form-domain hypotheses. Positive $\epsilon$
gives local Euclidean regularity through the original derivatives:

$$
 \partial_x f=Uf+\frac y2 Zf,\qquad
 \partial_y f=Vf-\frac x2 Zf,\qquad
 \partial_z f=Zf.
 \tag{15.8}
$$

For each compact smooth cutoff $\chi$, the product rule on the
defining core, followed by its $\mathcal H_\epsilon$ closure, gives

$$
 \|\chi f\|_{H^1(\mathbb R^3)}^2
       \le C_{\chi,\epsilon}\bigl(T[f]+\|f\|_2^2\bigr),
 \qquad f\in\mathcal H_\epsilon .
 \tag{15.9}
$$

Only local regularity is asserted here. In particular (15.9)
makes no global identification of the free domain with an
isotropic Euclidean Sobolev space.

Choose a bounded source neighbourhood $K$ and a cutoff equal to
one on $K$. Since $M\in L^{7/4}(K)$, its truncated high part
satisfies

$$
 \|M\mathbf1_{K\cap\{M>B\}}\|_{3/2}\longrightarrow0
          \qquad(B\longrightarrow\infty).
 \tag{15.10}
$$

Hölder and the classical three-dimensional Sobolev inequality bound
its potential integral by the left side of (15.10) times
$\|\chi f\|_6^2$. The part of $M$ at most $B$ on $K$ contributes
at most $B\|f\|_2^2$, and $M$ is bounded on the complement of $K$.
Using (15.9) and choosing $B$ sufficiently large proves

$$
 \text{for every }d>0\text{ there is }C_d<\infty
 \text{ such that }\quad
 W[f]\le dT[f]+C_d\|f\|_2^2
 \quad(f\in\mathcal H_\epsilon).
 \tag{15.11}
$$

Take $d<1/g$. The classical KLMN theorem applies to the densely
defined closed nonnegative form $T$ and the Hermitian perturbation
$-gW$. It yields closedness on exactly the same domain and

$$
 q[f]\ge(1-gd)T[f]-gC_d\|f\|_2^2.
 \tag{15.12}
$$

Its shifted form norm is equivalent to the original free form
norm, so the original compact smooth core stays a form core.
The closed-form representation theorem therefore defines the
self-adjoint Friedrichs operator in (15.2).

For the essential spectrum we check compactness in this same
realization. The map

$$
 J:\mathcal H_\epsilon\longrightarrow L^2(d\xi),
       \qquad Jf=\sqrt M\,f
 \tag{15.13}
$$

is compact when the source has norm
$(T[f]+\|f\|_2^2)^{1/2}$. Indeed, a sequence bounded in that norm
is locally bounded in Euclidean $H^1$ by (15.9). The classical
Rellich compactness theorem gives, after a diagonal subsequence,
local convergence in $L^{14/3}$, since $14/3<6$.
Hölder with $M\in L^{7/4}$ gives convergence of $Jf$ in $L^2$
on each bounded set. On its complement, (15.7) makes the
weighted tails uniformly small, because the unweighted $L^2$
norms are bounded. Thus the subsequence is Cauchy in the whole
target space of (15.13).

Let $L$ be the free self-adjoint operator of $T$. For sufficiently
large $s>0$ define

$$
 S_s=(L+s)^{-1/2},\qquad B_s=JS_s,\qquad K_s=B_s^*B_s.
 \tag{15.14}
$$

The map $S_s$ is bounded into the free form domain, so $B_s$
and $K_s$ are compact. Estimate (15.11) gives
$\|K_s\|\le d+C_d/s$. Choose first $gd<1$ and then $s$ large
enough that $g\|K_s\|<1$. The variational representation of
$q+s$ gives

$$
\begin{aligned}
 (A_{n,\epsilon,g}+s)^{-1}
     &=S_s(I-gK_s)^{-1}S_s,\\
 (A_{n,\epsilon,g}+s)^{-1}-(L+s)^{-1}
     &=gS_s(I-gK_s)^{-1}K_sS_s.
\end{aligned}
\tag{15.15}
$$

The second line is compact. This argument uses relative form
compactness; it does not require multiplication by $M$ to be
bounded on unweighted $L^2$ or to have the free operator domain.

For completeness the whole free essential spectrum has an
explicit singular Weyl family. Fix $\lambda\ge0$,
$k=\sqrt\lambda$, and $\phi\in C_c^\infty(\mathbb R^3;\mathbb C)$
with $\|\phi\|_2=1$. Put

$$
 \phi_a=a^{-2}\phi\circ\delta_{1/a},
       \qquad u_a=e^{ikx}\phi_a .
 \tag{15.16}
$$

The retained Jacobian is $a^4$, so $\|u_a\|_2=1$. Their norms on
each fixed compact set tend to zero, and hence $u_a\rightharpoonup0$
in $L^2$. Compact smooth tests belong to $D(L)$ by integration by
parts and the defining form-core approximation. With
$L_H=-U^2-V^2$, direct differentiation gives

$$
\begin{aligned}
 (L-\lambda)u_a
    &=e^{ikx}(L_H\phi_a-\epsilon^2Z^2\phi_a-2ikU\phi_a),\\
 \|(L-\lambda)u_a\|_2
    &\le a^{-2}\|L_H\phi\|_2
       +\epsilon^2a^{-4}\|Z^2\phi\|_2
       +2k a^{-1}\|U\phi\|_2
       \longrightarrow0 .
\end{aligned}
\tag{15.17}
$$

The singular Weyl criterion puts every $\lambda\ge0$ in
$\sigma_{\mathrm{ess}}(L)$. Nonnegativity of $L$ gives the reverse
containment. The compact resolvent difference (15.15) and the
classical Weyl theorem now prove (15.2), in both directions.

Finally use one of the actual zero-noise annular trials supplied
by (13.9)--(13.11). Since $g>\lambda_n$, choose one fixed
nonzero compact smooth $h$, supported away from the pole, with

$$
 \|h\|_2=1,\qquad
 \mathcal E_H[h]-gW_{n,0}[h]<0.
 \tag{15.18}
$$

Its support lies between gauge radii $r_->0$ and $r_+<\infty$.
Set $h_a=a^{-2}h\circ\delta_{1/a}$. Each $h_a$ is a normalized
test in the original fixed-$\epsilon$ core. Exact scaling gives

$$
 q[h_a]=a^{-2}
 \left(\mathcal E_H[h]+\epsilon^2a^{-2}\|Zh\|_2^2
                          -gW_{n,\epsilon/a}[h]\right).
 \tag{15.19}
$$

The locally uniform off-pole limit from Theorem 10.2 makes the
parenthesis tend to the strictly negative number in (15.18).
Thus $q[h_a]<0$ for every sufficiently large $a$. Choose such
scales with $a_{j+1}>(r_+/r_-)a_j$. The corresponding supports
are separated annuli. Locality of the original derivatives and
the multiplication form gives

$$
 q\left[\sum_{j=1}^N c_jh_{a_j}\right]
       =\sum_{j=1}^N|c_j|^2q[h_{a_j}]<0
          \quad\text{whenever }(c_1,\ldots,c_N)\ne0 .
 \tag{15.20}
$$

The form-domain variational principle makes the negative spectral
projection have dimension at least $N$ for every $N$.
By (15.2), each negative spectral point is an isolated eigenvalue
of finite multiplicity. Estimate (15.12) bounds their lower end;
an accumulation at a finite negative point would belong to the
essential spectrum. There are therefore infinitely many
eigenvalues, their only accumulation point is zero, and (15.3)
follows.

**Definition 15.3 (correspondence, attribution and spectral scope).**
The marginal in (15.4)--(15.7) is the original field of (10.2),
with both time endpoints retained. The sharp zero-noise annular
trials and their original-domain approximation are supplied by
§13; (15.19) uses the same complete scaling as §14.
The new model-specific bridges are the local integrability and
tail checks for this actual marginal, its relative form
compactness on the original positive-noise domain, the explicit
free Weyl family, and the separated actual-field negative
subspaces. The spectral consequence is repo-derived from these
checks and the stated suppliers, without a global-priority claim.

The generic closed-form, perturbation and variational results are
classical. In Gerald Teschl,
[*Mathematical Methods in Quantum Mechanics*, authorized online
first edition](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf),
Theorem 6.24, printed p.150, gives KLMN; Theorem 6.19,
printed p.146, gives essential-spectrum invariance under compact
resolvent difference; Lemma 6.26, printed pp.151--152, gives the
form-compact version. The singular Weyl criterion is Lemma 6.17,
printed pp.145--146, and the form-domain min-max statements are
Theorems 4.10 and 4.12(i), printed p.119. The Sobolev and Rellich
inputs in (15.9)--(15.13) are the classical three-dimensional
local embeddings, used with compact cutoffs and exponent
$14/3<6$. None of these generic statements alone verifies the
actual retained potential or the annular subspaces.

These conclusions concern the retained analytic reference form
at each fixed positive noise. They preserve the nonautonomous
retention statement and the separate parent collapse of
Theorem 10.2. They give no parameter-uniform lower bound, no
identification of an attractive zero-noise completion with the
positive-noise free domain, and no negative-eigenvalue counting
asymptotic.

## 追加锚（本行以下为增补区）

## 16. Quantitative lower counts for the original retained operator

**Definition 16.1 (fixed source, strict count and angular gap).**
Fix an integer $n\ge2$ and a real $g>\lambda_n=2\pi\mu_n$.
Retain Definition 10.1's identity unit source $\delta_0$ on
$H^n=\mathbb R^{2n}\times\mathbb R$, raw Lebesgue measure,
horizontal covariance-$2$ clock and independent central covariance
$2\epsilon^2$. In particular, for $\epsilon\ge0$ the potential is
exactly the complete same-source marginal

$$
M_{n,\epsilon}(X_1,z)
 =\int_0^\infty\int_{\mathbb R^{2n-2}}
 (e^{-tL_{n,\epsilon}}\delta_0)(X_1,W,z)\,dW\,dt,
\qquad
L_{n,\epsilon}=-\sum_{j=1}^n(U_j^2+V_j^2)-\epsilon^2Z^2.
\tag{16.1}
$$

The fields in this parent expression are those of (10.1).
Both time endpoints and the whole unweighted omitted fibre are
retained. Fix $\epsilon=1$ for the retained operator. On complex
$L^2(\mathbb R^3,dx\,dy\,dz)$ put
$U=\partial_x-(y/2)\partial_z$,
$V=\partial_y+(x/2)\partial_z$, $Z=\partial_z$ and

$$
\begin{aligned}
\mathcal E_H[f]&=\|Uf\|_2^2+\|Vf\|_2^2,\\
\mathcal H_1
 &=\overline{C_c^\infty(\mathbb R^3;\mathbb C)}^
 {\left(\|f\|_2^2+\mathcal E_H[f]+\|Zf\|_2^2\right)^{1/2}},\\
W_{n,\epsilon}[f]&=\int_{\mathbb R^3}M_{n,\epsilon}|f|^2\,dx\,dy\,dz,\\
q_1[f]&=\mathcal E_H[f]+\|Zf\|_2^2-gW_{n,1}[f],
\qquad D(q_1)=\mathcal H_1,\\
N_{n,g}(E)&=\dim_{\mathbb C}\operatorname{Ran}
 \mathbf1_{(-\infty,-E)}(A_{n,1,g}),\qquad E>0.
\end{aligned}
\tag{16.2}
$$

Here $A_{n,1,g}$ is exactly the Friedrichs operator associated
with (15.1). Its domain has no angular, radial or real-valued
restriction. Theorem 15.2 supplies lower semiboundedness and
negative discreteness with finite complex multiplicity and no
negative accumulation point. These imply $N_{n,g}(E)<\infty$
for each $E>0$.

Use $R$, $J=(-\pi/2,\pi/2)$, $c=\cos a$, $q_n$ and the natural
angular domain $\mathcal H_c$ of (12.3)--(12.4). For a nonzero
real $b\in C_c^\infty(J)$ define

$$
\begin{aligned}
A_b&=\int_J(4c|b'|^2+c|b|^2)\,da,&
Q_b&=\int_Jq_n|b|^2\,da,\\
C_b&=\int_Jc|b|^2\,da>0,&
D_b&=\frac{g}{2\pi}Q_b-A_b.
\end{aligned}
\tag{16.3}
$$

When $D_b>0$, write $\kappa_b=\sqrt{D_b/C_b}$.
The natural angular variational problem still has no imposed
endpoint traces. Compact angular functions here are only trials.
The analytic premises used below are the original marginal and
off-pole convergence of Theorem 10.2, the polar identities of
§12, the natural-endpoint approximations of §13, the complete
scaling of §14 and the form and spectral conclusions of §15.

**Theorem 16.2 (finite-energy geometric count and angular lower coefficient).**
With exactly Definition 16.1's source, parameters and full complex
operator, let
$h\in C_c^\infty(\mathbb R^3\setminus\{0\};\mathbb C)$ satisfy
$\|h\|_2=1$ and
$\gamma=gW_{n,0}[h]-\mathcal E_H[h]>0$.
Choose $0<r_-<r_+<\infty$ with
$\operatorname{supp}h\subset\{r_-\le R\le r_+\}$.
There exists $a_*\ge1$ such that, for every $a\ge a_*$,

$$
a^{-2}\|Zh\|_2^2\le\frac\gamma4,
\qquad
g\left|W_{n,1/a}[h]-W_{n,0}[h]\right|\le\frac\gamma4.
\tag{16.4}
$$

For any such $a_*$, any fixed $B>r_+/r_-$ and every $E>0$,

$$
\begin{aligned}
N_{n,g}(E)&\ge
 \max\left\{0,\left\lfloor
 \frac{\log\bigl(\gamma/(2a_*^2E)\bigr)}{2\log B}
 \right\rfloor\right\},\\
\liminf_{E\downarrow0}\frac{N_{n,g}(E)}{\log(1/E)}
 &\ge\frac1{2\log B}>0.
\end{aligned}
\tag{16.5}
$$

Such an $h$ exists for every fixed $n\ge2$ and $g>\lambda_n$.
More precisely, every nonzero real $b\in C_c^\infty(J)$ with
$D_b>0$ gives the bound

$$
\liminf_{E\downarrow0}\frac{N_{n,g}(E)}{\log(1/E)}
 \ge\frac1{2\pi}\sqrt{\frac{D_b}{C_b}}>0.
\tag{16.6}
$$

The set of these $b$ is nonempty for every such $n,g$.
Consequently the supremum of the right side of (16.6) over this
set is also an extended lower bound; no finiteness of that
supremum is asserted.

**Proof.** First fix any $h$ in the statement. Its compact support
avoids the pole, so the locally uniform off-pole convergence in
Theorem 10.2 implies $W_{n,1/a}[h]\to W_{n,0}[h]$.
Also $\|Zh\|_2<\infty$. These facts give (16.4) simultaneously
for every $a$ beyond a single $a_*$ depending on the fixed trial,
$n$ and $g$.

For $\delta_a(x,y,z)=(ax,ay,a^2z)$ set
$h_a=a^{-2}h\circ\delta_{1/a}$. The raw Jacobian is $a^4$,
and the original derivative and complete-field scaling (14.9)
gives

$$
\begin{aligned}
\|h_a\|_2^2&=1,&
\mathcal E_H[h_a]&=a^{-2}\mathcal E_H[h],\\
\|Zh_a\|_2^2&=a^{-4}\|Zh\|_2^2,&
W_{n,1}[h_a]&=a^{-2}W_{n,1/a}[h],\\
q_1[h_a]
 &=a^{-2}\left(-\gamma+a^{-2}\|Zh\|_2^2
              +g\bigl(W_{n,0}[h]-W_{n,1/a}[h]\bigr)\right)
 \le-\frac\gamma{2a^2}\qquad(a\ge a_*).
\end{aligned}
\tag{16.7}
$$

Each $h_a$ is in the original fixed-noise compact smooth core.
Take $a_j=a_*B^j$ for integers $j\ge0$.
Their closed supports lie in
$\{a_jr_-\le R\le a_jr_+\}$ and are separated because
$B r_->r_+$. Locality of $U,V,Z$ and of the multiplication
potential therefore makes both the form and the $L^2$ norm
diagonal: for every finite complex coefficient family,

$$
\begin{aligned}
\left\|\sum_jc_jh_{a_j}\right\|_2^2&=\sum_j|c_j|^2,\\
(q_1+E\|\cdot\|_2^2)\left[\sum_jc_jh_{a_j}\right]
 &\le\sum_j|c_j|^2
       \left(E-\frac\gamma{2a_*^2B^{2j}}\right).
\end{aligned}
\tag{16.8}
$$

For a fixed $E>0$ put
$X=\log(\gamma/(2a_*^2E))/(2\log B)$ and
$k=\max\{0,\lfloor X\rfloor\}$.
If $k>0$, every integer $0\le j<k$ satisfies $j<X$,
including when $X$ is an integer. Thus each corresponding
parenthesis in (16.8) is strictly negative. The $k$ orthonormal
trials span a $k$-dimensional complex subspace on which
$q_1+E\|\cdot\|_2^2$ is strictly negative away from zero.
The classical form-domain min-max principle, as cited in
Definition 15.3, gives at least $k$ eigenvalues in the strict
interval $(-\infty,-E)$. For $k=0$ the inequality is automatic.
This proves the finite-$E$ assertion without counting an
eigenvalue at $-E$.

For fixed $h,a_*,B$, as $E\downarrow0$ the quantity $X$ is
$\log(1/E)/(2\log B)$ plus a constant. Taking a floor changes
it by less than one, and eventually $X>0$. Division by
$\log(1/E)$ proves the second line of (16.5).
Existence of at least one normalized compact annular $h$ with
positive $\gamma$ is supplied by (15.18). We next construct the
trials which give the sharper coefficient.

Since $g/(2\pi)>\mu_n$, the real compact angular approximations
(13.6)--(13.8), with $Q_n[b_j]\to1$ and $A[b_j]\to\mu_n$,
give a nonzero real $b$ for which $D_b>0$.
This uses the natural-endpoint cutoff argument, not Dirichlet
conditions on an angular minimizer. Now fix any such $b$ and
any $L>\pi/\kappa_b$.
The interval function $\sin(\pi\ell/L)$ belongs to
$H_0^1(0,L)$ and has derivative-to-function squared-norm ratio
$\pi^2/L^2<\kappa_b^2$.
Classical $H_0^1$ density by real compact smooth functions,
and continuity of both norms under this approximation, supply
$0\ne\psi\in C_c^\infty(0,L;\mathbb R)$ with

$$
\frac{\|\psi'\|_{L^2(0,L)}^2}{\|\psi\|_{L^2(0,L)}^2}
 <\frac{D_b}{C_b}.
\tag{16.9}
$$

This interval Dirichlet sine only constructs a trial; it imposes
no boundary condition on $A_{n,1,g}$.
Extend $\psi$ by zero and form the actual Cartesian function
$f=R^{-1}b(a)\psi(\log R)$.
Its radial support is compact in $1<R<e^L$ and its angular
support avoids both axes $\rho=0$. Extension by zero across
those axes is smooth, and the pole is avoided. Consequently
$f\in C_c^\infty(\mathbb R^3\setminus\{0\})$,
$\|Zf\|_2<\infty$, and $f$ belongs to the original
fixed-noise core.

Set $\ell=\log R$. The raw measure is
$R^4d\ell\,da\,d\theta/4$. In (12.12), the trial has
$v=b(a)\psi(\ell)$ and $v_\theta=0$.
Integration in $\theta$ contributes $2\pi$; the cross term
vanishes because $\int\psi\psi'=0$.
Using also $M_{n,0}=R^{-2}q_n/(2\pi)$ from (12.5) gives

$$
\begin{aligned}
\|f\|_2^2
 &=\frac\pi2\|b\|_{L^2(J)}^2
                 \int_0^Le^{2\ell}|\psi(\ell)|^2\,d\ell
 \in(0,\infty),\\
\mathcal E_H[f]
 &=\frac\pi2\left(C_b\|\psi'\|_2^2+A_b\|\psi\|_2^2\right),\\
W_{n,0}[f]&=\frac14 Q_b\|\psi\|_2^2,\\
\mathcal E_H[f]-gW_{n,0}[f]
 &=\frac\pi2\left(C_b\|\psi'\|_2^2-D_b\|\psi\|_2^2\right)<0.
\end{aligned}
\tag{16.10}
$$

Thus $h=f/\|f\|_2$ is admitted in (16.5), with $r_-=1$,
$r_+=e^L$ and positive gap
$\gamma=(\pi/2)(D_b\|\psi\|_2^2-C_b\|\psi'\|_2^2)/\|f\|_2^2$.
For this fixed $L$ and trial, every fixed $B>e^L$ gives
$\liminf N_{n,g}(E)/\log(1/E)\ge1/(2\log B)$ by first taking
$E\downarrow0$. Taking the supremum of these separate lower
bounds as $B\downarrow e^L$ gives $1/(2L)$.
For every $L>\pi/\kappa_b$ a trial can be chosen as above;
then letting $L\downarrow\pi/\kappa_b$ proves (16.6).
The constants $h,\gamma,a_*$ may change with $L$.
No uniform estimate for them is needed, since the $E$ limit
was taken separately for each fixed trial and $B$.
Finally the left side of (16.6) is the same extended real number
for all admitted $b$, so it bounds their supremum as stated.

**Definition 16.3 (attribution and the unresolved counting boundary).**
Theorem 16.2 is a repo-derived quantitative deduction for the exact
retained-source form, conditional on the analytic premises listed
in Definition 16.1. Its model-specific steps are the normalized
complete-field dilation, the uniform-in-$a\ge a_*$ error bounds
for each fixed annular trial, the disjoint complex trial spaces
and the angular trial's raw normalization. The min-max principle
is the classical result cited in Definition 15.3, and compact
smooth density in $H_0^1(0,L)$ and the sine quotient are classical
interval facts consumed in constructing (16.9). The natural
angular endpoint approximation is the one already proved in §13.
These suppliers are intermediate steps in the retained-source
deduction, not separate new counting theorems.

Hassell--Marshall,
[*Eigenvalues of Schrödinger operators with potential asymptotically
homogeneous of degree minus two*, Theorems 1--2](https://arxiv.org/abs/math/0510617v1),
concerns Euclidean Laplacians, scalar inverse-square tails and a
sphere angular operator under its stated remainder and threshold
hypotheses. No correspondence of its form and domain to the
present $U,V,Z$ form or of its sphere operator to the coupled
$(\sigma,m)$ expressions of (12.13) is established here.
Its counting coefficient and conclusions are not transferred.
No literature originality claim is attached to (16.5)--(16.6).

The count in (16.2) always concerns the original full complex
operator, although the lower bounds use a single family of
angular trials. Neither exhaustion of its angular modes nor an
all-mode counting density follows. A finite logarithmic upper
bound, finiteness of the variational supremum, an exact
coefficient and existence of a finite positive limit of
$N_{n,g}(E)/\log(1/E)$ remain unresolved. Pointwise finiteness
of $N_{n,g}(E)$ does not supply any of those assertions.

## 追加锚（本行以下为增补区）

## 17. A finite logarithmic upper count for the original retained operator

**Definition 17.1 (fixed source, full operator and gauge balls).**
Fix an integer $n\ge2$ and a real $g>\lambda_n=2\pi\mu_n$,
with the natural angular threshold of Definitions 12.1 and 13.1.
Retain the identity unit source $\delta_0$ on
$H^n=\mathbb R^{2n}\times\mathbb R$, the raw Lebesgue measure,
and the horizontal covariance-$2$ clock of Definition 10.1.
For $X=(X_1,W)$, $X_1=(x,y)$ and
$W\in\mathbb R^{2n-2}$, the potential is exactly

$$
\begin{aligned}
L_{n,\epsilon}
 &=-\sum_{j=1}^n(U_j^2+V_j^2)-\epsilon^2Z^2,\\
U_j&=\partial_{x_j}-\frac{y_j}{2}\partial_z,
\qquad V_j=\partial_{y_j}+\frac{x_j}{2}\partial_z,
\qquad Z=\partial_z,\\
M_{n,\epsilon}(x,y,z)
 &=\int_0^\infty\int_{\mathbb R^{2n-2}}
       (e^{-tL_{n,\epsilon}}\delta_0)(X_1,W,z)\,dW\,dt.
\end{aligned}
\tag{17.1}
$$

The parent free operator is the complex compact-smooth Friedrichs
closure. Both time endpoints and the whole unweighted omitted
fibre are retained. The independent central covariance is
$2\epsilon^2$. Set $\epsilon=1$ and $M=M_{n,1}$ throughout the
counting assertion. On complex $L^2(\mathbb R^3,d\xi)$ with
raw $d\xi=dx\,dy\,dz$, put

$$
\begin{aligned}
U&=\partial_x-\frac y2\partial_z,
&V&=\partial_y+\frac x2\partial_z,\\
\mathcal E_H[f]&=\|Uf\|_2^2+\|Vf\|_2^2,
&T_1[f]&=\mathcal E_H[f]+\|Zf\|_2^2,\\
\mathcal H_0
 &=\overline{C_c^\infty(\mathbb R^3;\mathbb C)}^
                 {(\|f\|_2^2+\mathcal E_H[f])^{1/2}},
&\mathcal H_1
 &=\overline{C_c^\infty(\mathbb R^3;\mathbb C)}^
                 {(\|f\|_2^2+T_1[f])^{1/2}},\\
q_1[f]&=T_1[f]-g\int M|f|^2\,d\xi,
&D(q_1)&=\mathcal H_1,\\
N_{n,g}(E)&=\dim_{\mathbb C}\operatorname{Ran}
   \mathbf1_{(-\infty,-E)}(A_{n,1,g}),
&E&>0.
\end{aligned}
\tag{17.2}
$$

Here $A_{n,1,g}$ is precisely Theorem 15.2's self-adjoint
operator of $q_1$, also used in (16.2). No symmetry or real-valued
restriction is imposed. Write

$$
\rho=(x^2+y^2)^{1/2},\qquad
R=(\rho^4+16z^2)^{1/4},\qquad B_r=\{\xi:R(\xi)<r\}.
\tag{17.3}
$$

The angular domain remains $\mathcal H_c$ of (12.4), with no
imposed endpoint traces. The ordinary analytic premises are the
original-field estimates and free realization in §§9--10, the
natural threshold in §§12--13, the complete-field scaling in §14,
and the closed original form in §15.

**Theorem 17.2 (supported comparison and finite upper rate).**
For every fixed $n,g$ of Definition 17.1 there are finite positive
constants $B,D$, independent of $E$, such that, on setting

$$
\begin{aligned}
H&=gB+\tfrac12+D,\\
c_0&=2\pi^2H^2+\frac{\pi^2D^2}{4}\log_+(D/4),
&c_1&=\frac{\pi^2D^2}{4},
\qquad \log_+(s)=\max\{0,\log s\}\quad(s>0),
\end{aligned}
\tag{17.4}
$$

the original full complex count satisfies

$$
\begin{aligned}
N_{n,g}(E)&\le e^2\bigl(c_0+c_1\log(1/E)\bigr)
                      &&(0<E<1),\\
N_{n,g}(E)&\le C_{n,g}\log(1/E)
                      &&(0<E<e^{-1}),\\
C_{n,g}&=e^2(c_0+c_1)\in(0,\infty).
\end{aligned}
\tag{17.5}
$$

**Proof.** We first retain the support of the singular-core
absorption remainder. Equations (15.4)--(15.5), for this same
complete marginal at $\epsilon=1$, give

$$
0<M(\rho,z)\le\frac1{4\pi\rho}\quad(\rho>0),
\qquad M\in L^{7/4}(B_1).
\tag{17.6}
$$

Indeed $B_1\subset\{0\le\rho<1,\ |z|<1/4\}$, and cylindrical
integration of the bound to the power $7/4$ has radial factor
$\rho^{-3/4}d\rho$, which is integrable at zero. The axis has
Lebesgue measure zero and is not removed from the form domain.
The original uniform off-pole estimate (15.6) at $\epsilon=1$
and its scaling consequence (15.7) give a finite positive
$C_n=C_{n,1}$ with

$$
M(\xi)\le C_nR(\xi)^{-2}\qquad(R\ge1).
\tag{17.7}
$$

In particular these are estimates of (17.1), with no change of
source or marginal.

Choose a real $\chi\in C_c^\infty(B_2)$ with
$0\le\chi\le1$ and $\chi=1$ on $\overline{B_1}$; a smooth
function of $R^4=\rho^4+16z^2$ gives such a choice. For
$f\in\mathcal H_1$, the distributional identities (15.8) imply,
on $B_2$, where $\rho\le2$,

$$
\begin{aligned}
\partial_xf&=Uf+\tfrac y2Zf,
&\partial_yf&=Vf-\tfrac x2Zf,
&\partial_zf&=Zf,\\
|\nabla f|^2&\le2(|Uf|^2+|Vf|^2)+3|Zf|^2.
\end{aligned}
\tag{17.8}
$$

The product rule first on the defining core and then by
$\mathcal H_1$ approximation gives $\chi f\in H^1(\mathbb R^3)$
and the supported estimate

$$
\|\nabla(\chi f)\|_2^2
 \le6T_1[f]+2\|\nabla\chi\|_\infty^2
                         \int_{B_2}|f|^2\,d\xi.
\tag{17.9}
$$

Consume here the classical complex three-dimensional Sobolev
inequality, the same local supply used in (15.9)--(15.11):
$\|u\|_6^2\le S_3\|\nabla u\|_2^2$ for compactly supported
$H^1$ functions. For example the finite constant
$C_0=S_3(6+2\|\nabla\chi\|_\infty^2)$ yields

$$
\|\chi f\|_6^2
 \le C_0\left(T_1[f]+\int_{B_2}|f|^2\,d\xi\right).
\tag{17.10}
$$

This is only a cutoff estimate. No global equality between
$\mathcal H_1$ and Euclidean $H^1$ is used.

For $B>0$ let $M_B=M\mathbf1_{B_1\cap\{M>B\}}$.
By (17.6), $\|M_B\|_{3/2}\to0$ as $B\to\infty$.
The fixed threshold is positive, so $g>\lambda_n$ implies $g>0$.
Choose one finite $B>0$ such that
$gC_0\|M_B\|_{3/2}\le1/2$. Hölder, $\chi=1$ on $B_1$,
and (17.10) give, for every $f\in\mathcal H_1$,

$$
g\int M_B|f|^2\,d\xi
 \le\tfrac12T_1[f]+\tfrac12\int_{B_2}|f|^2\,d\xi.
\tag{17.11}
$$

The remaining part of $M$ on $B_1$ is bounded by $B$;
use (17.7) on its complement. Put $D=gC_n>0$ and define the
bounded, nonnegative comparison potential

$$
V_{\mathrm{eff}}=(gB+\tfrac12)\mathbf1_{B_2}
             +DR^{-2}\mathbf1_{\{R\ge1\}}.
\tag{17.12}
$$

The second summand is defined as zero for $R<1$. Combining the
three pieces gives, on the original domain,

$$
\begin{aligned}
g\int M|f|^2\,d\xi
 &\le\tfrac12T_1[f]+\int V_{\mathrm{eff}}|f|^2\,d\xi,\\
q_1[f]&\ge\tfrac12T_1[f]-\int V_{\mathrm{eff}}|f|^2\,d\xi
 \ge\tfrac12\mathcal E_H[f]-\int V_{\mathrm{eff}}|f|^2\,d\xi.
\end{aligned}
\tag{17.13}
$$

Thus the mass remainder from absorption is supported in $B_2$.
There is no negative global constant in (17.13).
Moreover $V_{\mathrm{eff}}\le H$ and
$V_{\mathrm{eff}}=DR^{-2}$ for $R\ge2$.

We next obtain the horizontal counting supply on its full complex
free domain. Let $L_H$ be the nonnegative self-adjoint Friedrichs
operator of $\mathcal E_H$ on $\mathcal H_0$ and put $T=L_H/2$.
It has zero kernel. In fact if $L_Hf=0$, nonnegativity gives
$Uf=Vf=0$ in distributions. The identity $[U,V]=Z$ then gives
$Zf=0$. The coordinate identities in (17.8) show that every
coordinate derivative is zero. Such a distribution is constant,
and a constant in $L^2(\mathbb R^3)$ is zero. Hence
$\ker T=\{0\}$ as well.

For precisely this horizontal kinetic operator, the partial
central Fourier heat column is the one in (9.7), with the full
Friedrichs direct-integral/core correspondence of (9.8)--(9.10).
Its classical supplier is Krötz--Thangavelu--Xu,
[*The heat kernel transform for the Heisenberg group*, §4.1,
equation (4.1.2)](https://arxiv.org/abs/math/0401243v2).
With $\widehat f(X,k)=\int e^{-ikz}f(X,z)\,dz$ and inverse
factor $1/(2\pi)$, it reads

$$
\widehat h_H(t,\rho,k)
 =\frac{|k|}{4\pi\sinh(|k|t)}
      \exp\left(-\frac{|k|\rho^2}{4}\coth(|k|t)\right),
\qquad
\widehat h_H(t,\rho,0)=\frac{e^{-\rho^2/(4t)}}{4\pi t}.
\tag{17.14}
$$

The column is even in $k$, so the opposite Fourier sign in that
supplier has the same result. The Gaussian zero mode and the
factor $|k|t$ fix the covariance-$2$ clock and raw unit source.
Only the horizontal column is consumed; no inverse prefactor
from the supplier's full Laplace heat formula is transplanted.
Its radial pole column computes the heat kernel of the full
operator, rather than restricting its form domain to radial
functions. This is the same retained horizontal kinetic operator
in (17.2); its heat kernel does not replace $M_{n,1}$ by an
$n=1$ Green potential.

At the identity, inversion of (17.14) gives

$$
\begin{aligned}
h_H(t,0)
 &=\frac1{4\pi^2t^2}\int_0^\infty\frac{s}{\sinh s}\,ds,
&\int_0^\infty\frac{s}{\sinh s}\,ds
 &=2\sum_{j=0}^\infty\frac1{(2j+1)^2}=\frac{\pi^2}{4},\\
h_H(t,0)&=\frac1{16t^2}.
\end{aligned}
\tag{17.15}
$$

The integral follows by the nonnegative expansion
$1/\sinh s=2\sum_{j\ge0}e^{-(2j+1)s}$ and termwise
integration. Left translations preserve the compact smooth core
and its closure, so the kernel diagonal is constant in space.
Consequently the heat kernel of $T=L_H/2$ has diagonal
$h_H(t/2,0)=1/(4t^2)$. For every measurable
$\Omega\subset\mathbb R^3$ of finite measure and every
$\phi\in\mathbb C$,

$$
\operatorname{Tr}_{L^2}\left[
 \mathbf1_\Omega\bigl(\phi,e^{-tT}\phi\bigr)_{\mathbb C}
                      \mathbf1_\Omega\right]
 =\frac{|\phi|^2|\Omega|}{4t^2}.
\tag{17.16}
$$

This local trace identity also follows without a pointwise trace
assumption: factor the localized operator through
$e^{-tT/2}\mathbf1_\Omega$ and use its squared Hilbert--Schmidt
norm; the convolution semigroup identity integrates the squared
kernel to the displayed diagonal. This works for every such
measurable $\Omega$, not only smooth bounded sets.

Consume now Rupert L. Frank,
[*Cwikel's theorem and the CLR inequality*, Theorem 3.2 and
Lemma 3.4](https://arxiv.org/abs/1206.3325v1), with the
sigma-finite space $X=(\mathbb R^3,d\xi)$, separable fibre
$\mathbb C$ and exponent $\nu=4$. In Lemma 3.4 the localized
heat constant in (17.16) is
$C'=|\Omega||\phi|^2/4$. Its heat-to-spectral and
spectral-to-inverse constants are, respectively,

$$
B'=C'(2e/\nu)^{\nu/2}
   =\frac{e^2}{16}|\Omega||\phi|^2,
\qquad
A'=B'\frac{\nu}{\nu-2}
   =\frac{e^2}{8}|\Omega||\phi|^2.
\tag{17.17}
$$

Thus, for every $s>0$, all finite-measure $\Omega$ and all
$\phi\in\mathbb C$, Theorem 3.2's condition (3.4) is verified:

$$
\operatorname{Tr}_{L^2}\left[
 \mathbf1_\Omega
 \bigl(\phi,T^{-1}\mathbf1_{(0,s]}(T)\phi\bigr)_{\mathbb C}
 \mathbf1_\Omega\right]
 \le\frac{e^2}{8}s|\Omega||\phi|^2.
\tag{17.18}
$$

Together with $\ker T=\{0\}$, this supplies that theorem's
$A=e^2/8$. Use its general constant
$C_\nu=(\nu/2)(\nu/(\nu-2))^{\nu-2}$, so $C_4=8$.
For any bounded nonnegative compactly supported measurable $F$,
the potential $-F$ is self-adjoint and compact on the
one-dimensional fibre, and $\int F^2\,d\xi<\infty$.
Bounded multiplication gives a closed lower semibounded form on
$\mathcal H_0$. The consumed CLR estimate therefore yields

$$
\dim_{\mathbb C}\operatorname{Ran}
 \mathbf1_{(-\infty,0)}(T-F)
 \le C_4A\int F^2\,d\xi
 =e^2\int F^2\,d\xi.
\tag{17.19}
$$

This is an intermediate specialization of Frank's theorem. Its
count is strict and uses complex multiplicities throughout.

For each $E>0$ set $F_E=(V_{\mathrm{eff}}-E)_+$.
This function is bounded, nonnegative and measurable. Outside
$B_2$ it vanishes whenever $R\ge\sqrt{D/E}$, so its support is
contained in the compact set
$\{R\le\max\{2,\sqrt{D/E}\}\}$; hence $F_E\in L^2$ for each
$E>0$. From (17.13) and
$E-V_{\mathrm{eff}}\ge-(V_{\mathrm{eff}}-E)_+$,

$$
q_1[f]+E\|f\|_2^2
 \ge\tfrac12\mathcal E_H[f]-\int F_E|f|^2\,d\xi
 \qquad(f\in\mathcal H_1).
\tag{17.20}
$$

The defining core norm of $\mathcal H_0$ is bounded by that of
$\mathcal H_1$. Core approximation, with the same $L^2$ limit
and distributional derivatives, gives the continuous inclusion
$\mathcal H_1\subset\mathcal H_0$.
Every finite-dimensional complex subspace strictly negative for
the left side of (17.20) is therefore a subspace of
$\mathcal H_0$ strictly negative for its right side.

Here the strict form index equals the rank of the strict
negative spectral projection. Indeed for any lower semibounded
self-adjoint operator its negative spectral range lies in its
form domain, since its negative spectral interval is bounded.
Every nonzero vector in that range has strictly negative form.
Conversely, a subspace whose dimension exceeds that rank
contains a nonzero vector orthogonal to the negative spectral
range; its form is nonnegative by the spectral theorem.
The same reasoning with arbitrarily large finite subspaces
covers infinite rank. This is the classical form-domain
min-max principle cited in Definition 15.3 (Teschl,
Theorems 4.10 and 4.12(i)), applied to these two forms.
It proves the required comparison direction and then (17.19)
gives

$$
N_{n,g}(E)
 \le\dim_{\mathbb C}\operatorname{Ran}
       \mathbf1_{(-\infty,0)}(T-F_E)
 \le e^2\int F_E^2\,d\xi.
\tag{17.21}
$$

An original eigenvalue equal to $-E$ has zero shifted form and
is excluded. The comparison uses the larger horizontal domain
only for this index bound; every angular mode of the original
complex operator is counted.

It remains to evaluate the integral with the raw gauge volume.
In (12.3)'s coordinates,
$\rho^2=R^2\cos a$, $4z=R^2\sin a$,
$-\pi/2<a<\pi/2$ and $0\le\theta<2\pi$.
Writing $u=\rho^2$ gives
$\rho\,d\rho\,dz=\tfrac12du\,dz
=(R^3/4)dR\,da$. Thus

$$
d\xi=\frac{R^3}{4}\,dR\,da\,d\theta,
\qquad
\int G(R)\,d\xi=\frac{\pi^2}{2}\int_0^\infty G(R)R^3\,dR,
\qquad |B_2|=2\pi^2
\tag{17.22}
$$

for nonnegative radial $G$. On $B_2$ we have $F_E\le H$.
On $R\ge2$, $F_E\le DR^{-2}$ and it is zero beyond
$\sqrt{D/E}$. Therefore, for every $E>0$,

$$
\begin{aligned}
\int F_E^2\,d\xi
 &\le2\pi^2H^2+
 \begin{cases}
 \displaystyle\frac{\pi^2D^2}{2}
       \int_2^{\sqrt{D/E}}\frac{dR}{R},&\sqrt{D/E}>2,\\
 0,&\sqrt{D/E}\le2
 \end{cases}\\
 &=2\pi^2H^2+\frac{\pi^2D^2}{4}\log_+\left(\frac D{4E}\right).
\end{aligned}
\tag{17.23}
$$

The positive logarithm includes the empty-tail case $E\ge D/4$.
For $0<E<1$,
$\log_+(D/(4E))\le\log(1/E)+\log_+(D/4)$.
Equations (17.21)--(17.23) yield the first line of (17.5)
with (17.4). If $0<E<e^{-1}$, then $\log(1/E)>1$, and
$c_0+c_1\log(1/E)\le(c_0+c_1)\log(1/E)$.
This proves all of (17.5). Every constant was fixed after
$n,g$ and before $E$. The CLR bound was applied only to each
compactly supported $F_E$, never to the untruncated tail at
$E=0$.

**Corollary 17.3 (two-sided logarithmic order and a finite variational supremum).**
For every integer $n\ge2$ and every fixed $g>\lambda_n$, with
exactly the operator and count of Definition 17.1,

$$
0<\liminf_{E\downarrow0}\frac{N_{n,g}(E)}{\log(1/E)}
 \le\limsup_{E\downarrow0}\frac{N_{n,g}(E)}{\log(1/E)}
 <\infty.
\tag{17.24}
$$

For $J=(-\pi/2,\pi/2)$, $c=\cos a$ and $q_n$ of (12.3), put,
for each nonzero real $b\in C_c^\infty(J)$,

$$
C_b=\int_Jc|b|^2\,da>0,\qquad
D_b=\frac{g}{2\pi}\int_Jq_n|b|^2\,da
       -\int_J(4c|b'|^2+c|b|^2)\,da,
\qquad
\mathcal B_{n,g}=\{0\ne b\in C_c^\infty(J;\mathbb R):D_b>0\}.
\tag{17.25}
$$

This class is nonempty and its angular variational supremum
satisfies

$$
0<S_{n,g}:=\sup_{b\in\mathcal B_{n,g}}
               \frac1{2\pi}\sqrt{\frac{D_b}{C_b}}
 \le\liminf_{E\downarrow0}\frac{N_{n,g}(E)}{\log(1/E)}
 \le\limsup_{E\downarrow0}\frac{N_{n,g}(E)}{\log(1/E)}
 \le e^2c_1<\infty.
\tag{17.26}
$$

**Proof.** Theorem 16.2 gives nonemptiness of $\mathcal B_{n,g}$
and, for every individual $b$ in that class, precisely (16.6)
for this same full count. Theorem 17.2, divided by $\log(1/E)$
and followed by $E\downarrow0$, gives the common finite upper
bound $e^2c_1$ on the limsup. Write $L_-$ and $L_+$ for these
liminf and limsup. They are now finite and satisfy
$L_-\le L_+\le e^2c_1$. For every
$b\in\mathcal B_{n,g}$, (16.6) gives
$0<(2\pi)^{-1}\sqrt{D_b/C_b}\le L_-$.
Taking the supremum over this nonempty class proves (17.26),
including its strict positivity and finiteness, and hence (17.24).
The $E$ limits here belong to the common original count; no
uniform estimate on the lower theorem's individual trials is
required.

**Definition 17.4 (attribution and the remaining counting boundary).**
Theorem 17.2 is a source-specific ordinary deduction conditional
on Definition 17.1's analytic premises. Its application consists
of the supported core absorption for the actual whole marginal,
the full-domain strict-index comparison and the raw gauge-tail
integral. The classical heat column of Krötz--Thangavelu--Xu,
Frank's heat-trace/CLR results, the cutoff Sobolev inequality and
the form-domain min-max principle are consumed at their stated
places inside that deduction; they are not new general theorems
here. Corollary 17.3 combines that upper bound with the exact
every-$b$ lower inequality of Theorem 16.2. These applications
carry no literature-priority claim.

In particular the finite upper rate and finiteness of the
variational supremum left unresolved in Definition 16.3 follow
under these premises. The full complex multiplicities, all
angular modes and the natural angular endpoints are retained.
The constants depend on each fixed $n,g$; no uniformity in either
parameter is asserted.

The following fully quantified counting-limit statement remains
unresolved: for every integer $n\ge2$ and every real
$g>\lambda_n$, does there exist $L_{n,g}\in(0,\infty)$ such that,
for the original source, clock, whole marginal, $\epsilon=1$,
full complex $\mathcal H_1$ operator and strict count in
(17.1)--(17.2),

$$
\lim_{E\downarrow0}\frac{N_{n,g}(E)}{\log(1/E)}=L_{n,g}\ ?
\tag{17.27}
$$

Neither an exact all-mode coefficient nor convergence follows
from (17.24)--(17.26). In particular those inequalities do not
identify $S_{n,g}$ with a counting limit. Such a conclusion would
require an asymptotic density for the full coupled modes and a
justified error comparison transferring it to the original
positive-noise potential.

## 追加锚（本行以下为增补区）

## 18. The conditional logarithmic counting limit and its all-mode coefficient

**Definition 18.1 (the fixed count and natural angular fibres).**
Fix an integer $n\ge2$. Retain exactly the identity unit source,
raw Lebesgue measures, covariance-$2$ heat clock, complete time
integral and whole unweighted $W\in\mathbb R^{2n-2}$ marginal in
(17.1). The central noise is fixed at $\epsilon=1$. The operator
$A_{n,1,g}$ and strict complex count $N_{n,g}(E)$ are those of
(17.2), on the full original free closure $\mathcal H_1$, with no
symmetry or extra trace restriction. Use $J,c,I_n,q_n,\mathcal H_c,A$
of (12.3)--(12.4), $Q_n,q_*,\mu_n$ of (13.1), and
$\lambda_n=2\pi\mu_n$. Thus $0<q_*\le q_n\le1$.

The analytic hypotheses are the original-field formulas and
locally uniform off-pole convergence of Theorem 10.2, the full
complex polar identity (12.12)--(12.13), the closed natural angular
form and compact embedding supplied by V, Theorem 10.2 at the
revision in Definition 1.1, the natural-core approximation
(13.6)--(13.8), the complete-field scaling (14.9), and the original
closed form, compact smooth core and local estimates
(15.9)--(15.12). All conclusions below are ordinary conditional
analysis under these hypotheses.

For real $g>0$, put $k=g/(2\pi)$. On complex $L^2(J,da)$ define

$$
\begin{aligned}
D_0&=\mathcal H_c,\\
D_m&=\left\{b\in\mathcal H_c:
       \int_J\frac{\sin^2a}{c(a)}|b|^2\,da<\infty\right\}
                      &&(m\in\mathbb Z\setminus\{0\}),\\
h_{n,g}(\sigma,m)[b]
 &=A[b]+\int_J c(a)(\sigma+m\tan a)^2|b|^2\,da-kQ_n[b],
 &D(h_{n,g}(\sigma,m))&=D_m,\qquad \sigma\in\mathbb R.
\end{aligned}
\tag{18.1}
$$

Let $H_{n,g}(\sigma,m)$ be the self-adjoint operator of this form,
and set

$$
\nu_{n,g}(\sigma,m)
 =\dim_{\mathbb C}\operatorname{Ran}
       \mathbf1_{(-\infty,0)}(H_{n,g}(\sigma,m)),\qquad
 d_{n,g}=\frac1{2\pi}\sum_{m\in\mathbb Z}
                  \int_{\mathbb R}\nu_{n,g}(\sigma,m)\,d\sigma.
\tag{18.2}
$$

The domains in (18.1) are natural finite-energy domains; the extra
integral for $m\ne0$ is exactly integrability of the full square,
not a prescribed angular endpoint value. Finiteness of (18.2)
and the existence of these operators are included in the proof below.

**Theorem 18.2 (the original retained count and all-mode phase integral).**
Under Definition 18.1's analytic hypotheses, for every integer
$n\ge2$ and every fixed real $g>\lambda_n$,

$$
\begin{aligned}
0<L_{n,g}&=\frac{d_{n,g}}2
 =\frac1{4\pi}\sum_{m\in\mathbb Z}
        \int_{\mathbb R}\nu_{n,g}(\sigma,m)\,d\sigma<\infty,\\
N_{n,g}(E)&=L_{n,g}\log(1/E)+o(\log(1/E))
                                      \qquad(E\downarrow0).
\end{aligned}
\tag{18.3}
$$

For fixed $n$, the coefficient $L_{n,g}$ is continuous in
$g>\lambda_n$. Every integer angular mode and its complex
multiplicity is included, including couplings at which an
angular channel has a zero eigenvalue.

**Proof.** Fix $n$. The construction of the coefficient will use
all $g>0$; the original counting conclusion uses $g>\lambda_n$.
First consider the nonnegative part of (18.1). The sum of the
closed form $A$ and the nonnegative multiplication square is
closed on its intersection domain. This domain is $D_m$ because

$$
c(\sigma+m\tan a)^2
 =m^2\frac{\sin^2a}{c}+2m\sigma\sin a+\sigma^2c.
\tag{18.4}
$$

The last two multipliers are bounded. The domain is dense since
it contains $C_c^\infty(J;\mathbb C)$. Its embedding into $L^2(J)$
is compact, being continuously contained in $\mathcal H_c$ with
its form norm. The bounded Hermitian perturbation $-kq_n$
therefore gives a closed lower semibounded form and a
self-adjoint compact-resolvent operator, with $H_{n,g}\ge-k$.
These are the classical closed-form representation and compact
form-embedding implications, applied to the stated natural domain.

The compact angular core has exactly that domain as its form
closure. For $m=0$, bounded truncation of real and imaginary parts,
then (13.6)--(13.7)'s logarithmic endpoint cutoffs, and interior
mollification prove density in $\mathcal H_c$. For $m\ne0$, use
the same cutoffs $\eta_\varepsilon$. At endpoint distance $s$,
$c\asymp s$, $\sin^2a/c\asymp s^{-1}$ and

$$
c|\eta_\varepsilon'|^2
 \le \frac{C}{s\log(1/\varepsilon)^2}
             \mathbf1_{\{\varepsilon^2<s<\varepsilon\}}.
\tag{18.5}
$$

Multiplication by $|b|^2$ and the extra integrability in $D_m$
make this derivative cost tend to zero. The removed weighted
potential, derivative and $L^2$ tails also tend to zero.
Interior mollification then converges in the entire positive
form norm. This proves core density without changing either
natural angular endpoint to a Dirichlet endpoint.

Next there is a bounded region containing every contributing
frequency and mode. More precisely, for each finite $K$, the set
of pairs $(\sigma,m)\in\mathbb R\times\mathbb Z$ for which some
$\|b\|_2=1$ satisfies

$$
A[b]+\int_Jc(\sigma+m\tan a)^2|b|^2\,da\le K
\tag{18.6}
$$

is bounded. Otherwise choose such pairs with
$r_j=(\sigma_j^2+m_j^2)^{1/2}\to\infty$ and normalized functions
$b_j$. Compactness of the $A$ form embedding gives, along a
subsequence, $b_j\to b$ strongly in $L^2(J)$, $\|b\|_2=1$.
Also $(\sigma_j/r_j,m_j/r_j)\to(s,t)$ with $s^2+t^2=1$.
Divide the square bound by $r_j^2$. On each compact subinterval
of $J$, strong convergence and uniform convergence of its
multiplier imply $c(s+t\tan a)^2|b|^2=0$ almost everywhere.
The function $s+t\tan a$ has at most one zero in $J$, and is
not identically zero. Thus $b=0$ almost everywhere, a contradiction.
This argument also applies to real $m$ whenever that is useful.

If $h_{n,g}(\sigma,m)[b]\le0$ for a unit vector, (18.6) holds
with $K=k$. Moreover $h_{n,g}\ge A-k$, so its nonpositive
spectral rank is at most the number of eigenvalues of the
operator of $A$ in $(-\infty,k]$, which is finite. Taking a larger
$K$ gives the same bounded-support and rank conclusions for
bounded spectral thresholds. These bounds are uniform for $g$
in a fixed compact subset of $(0,\infty)$. In particular, only
finitely many integers $m$ can contribute to (18.2).

For a fixed such $m$, (18.4) gives a bounded polynomial
perturbation of $H_{n,g}(0,m)$, with the same operator domain.
Writing $R_m=(H_{n,g}(0,m)+k+1)^{-1}$, one obtains

$$
H_{n,g}(z,m)R_m
 =I+\bigl(2mz\sin a+z^2c-k-1\bigr)R_m,
                       \qquad z\in\mathbb C.
\tag{18.7}
$$

The right side is a holomorphic family of identity plus compact
operators on $L^2(J)$, hence Fredholm of index zero on the
connected domain $\mathbb C$. By (18.6) with $K=k+1$, it is
invertible for some sufficiently large real $z$. Analytic
Fredholm theory, in Dyatlov--Zworski, *Mathematical Theory of
Scattering Resonances*, version 1.0, Theorem C.8, printed p.522
([author text](https://math.mit.edu/~dyatlov/res/res_final.pdf)),
therefore makes its noninvertibility set discrete. There are
only finitely many real zeros in the compact contributing
interval. Away from them the strict negative index is locally
constant, by norm-resolvent continuity of the bounded
perturbation. Thus $\nu_{n,g}(\cdot,m)$ is bounded, compactly
supported and constant on finitely many intervals apart from
finitely many points. It is Riemann integrable.

For continuity in $g$, fix $g_0>0$ and a compact positive
coupling neighbourhood. The support and rank bounds just proved
are common throughout that neighbourhood. For each fixed $m$,
except at the finitely many real zeros for $g_0$, the bounded
perturbation $-(g-g_0)q_n/(2\pi)$ preserves the negative index
for sufficiently small $|g-g_0|$. Dominated convergence over
finitely many modes and a fixed bounded frequency interval gives
$d_{n,g}\to d_{n,g_0}$. This includes $g_0$ with a zero channel.
For $g>\lambda_n$, the attained natural minimizer of $A/Q_n$
has $h_{n,g}(0,0)[b]<0$. The strict inequality persists on an
open interval of $\sigma$ about zero. Consequently
$0<d_{n,g}<\infty$ in the required supercritical range.

We now relate this phase integral to finite log intervals.
Use unitary Fourier series in the actual $2\pi$ circle
$\mathbb T$, and write $v_m(\ell,a)=e^{-ima/2}w_m(\ell,a)$.
For a log interval of length $T$, define the auxiliary form

$$
\mathcal Q_g[w]=\sum_{m\in\mathbb Z}\int_0^T\int_J
 \left\{4c|\partial_aw_m|^2+c|w_m|^2
       +c|\partial_\ell w_m+im\tan a\,w_m|^2
       -kq_n|w_m|^2\right\}\,da\,d\ell.
\tag{18.8}
$$

Its norm $\|w\|^2=\sum_m\int_0^T\int_J|w_m|^2$ is the cylinder
$L^2$ norm. Take the positive-form closure of finite sums of
smooth longitudinal functions and compact smooth angular
functions. Periodic longitudinal functions define the periodic
realization; functions compactly supported in $(0,T)$ define
the realization with Dirichlet log interfaces. Angular closures
remain the natural ones proved above in both cases. Denote their
strict negative indices by $P_g(T)$ and $D_g(T)$, respectively.
Fourier series in the periodic variable give precisely the
operators (18.1) at $\sigma=2\pi j/T$, $j\in\mathbb Z$. The
support argument for every finite $K$, together with compactness
in each angular fibre, also gives compact resolvent for this
periodic realization. Its lower bound is $-k$.

The form-domain variational principle therefore gives

$$
\begin{aligned}
P_g(T)&=\sum_{m,j\in\mathbb Z}
                 \nu_{n,g}(2\pi j/T,m)=d_{n,g}T+O_{n,g}(1),\\
D_g(T)&\le P_g(T).
\end{aligned}
\tag{18.9}
$$

For the first equality and its error, count the lattice points
in each of the finitely many intervals of constancy of $\nu$.
Each interval contributes its length times $T/(2\pi)$ with a
bounded error. The finitely many threshold points contribute
another bounded error, with their strict counts retained.
The second inequality uses the embedding of the Dirichlet log
form domain into the periodic one; it imposes no angular trace.
Here and below the variational principle is the classical
form-domain result in Teschl, *Mathematical Methods in Quantum
Mechanics*, authorized online first edition, Theorems 4.10 and
4.12(i), printed p.119
([author text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf)).
It identifies a strict negative spectral rank with the supremum
of dimensions of strictly negative complex form subspaces.

For the reverse density, fix $\delta>0$ and let $S_T$ be the
periodic spectral subspace below $-\delta$. Repeating the same
Fredholm argument for $H_{n,g}+\delta$ gives

$$
r_T:=\dim S_T=d_\delta T+O_{n,g,\delta}(1),\qquad
 d_\delta=\frac1{2\pi}\sum_m\int_{\mathbb R}
  \dim\operatorname{Ran}\mathbf1_{(-\infty,-\delta)}
                 (H_{n,g}(\sigma,m))\,d\sigma.
\tag{18.10}
$$

The common bounded support and rank imply $d_\delta\uparrow d_{n,g}$
as $\delta\downarrow0$. Choose an orthonormal basis of $S_T$
consisting of longitudinal Fourier modes and angular eigenvectors.
The sum of their squared angular norms at each $\ell$ is $r_T/T$.
If $T>2h$, the positive operator on $S_T$ given by the mass in
$B_h=(0,h)\cup(T-h,T)$ has trace $2hr_T/T$. Removing its
eigenvectors with eigenvalue greater than $\varepsilon$ costs
at most $2hr_T/(T\varepsilon)=O_{h,\varepsilon,\delta}(1)$
dimensions. On the retained subspace $S'_T$,
$\int_{B_h}|w|^2\le\varepsilon\|w\|^2$.

Take a real smooth $0\le\chi\le1$, zero near the log endpoints,
one outside $B_h$, with $|\chi'|\le C/h$. If $H^{\rm per}_g$
is the operator of (18.8), its restriction to $S_T$ has norm
at most $k$. The product rule for
$\partial_\ell+im\tan a$ gives the exact identity and estimate

$$
\begin{aligned}
\mathcal Q_g[\chi w]
 &=\operatorname{Re}\langle H^{\rm per}_gw,\chi^2w\rangle
       +\sum_m\int c|\chi'|^2|w_m|^2\\
 &\le\bigl(-\delta+k\sqrt\varepsilon+C^2/h^2\bigr)\|w\|^2,
                      \qquad w\in S'_T.
\end{aligned}
\tag{18.11}
$$

Indeed $\|(1-\chi^2)w\|\le\sqrt\varepsilon\|w\|$.
Choose $\varepsilon<1$ small and $h$ large, both independent of
$T$, so that (18.11) is at most $-\delta\|w\|^2/2$.
The cutoff map is injective since
$\|\chi w\|^2\ge(1-\varepsilon)\|w\|^2$.
It follows that $D_g(T)\ge d_\delta T-O_{n,g,\delta}(1)$.
Together with (18.9), first taking $T\to\infty$ and then
$\delta\downarrow0$ proves

$$
\lim_{T\to\infty}\frac{D_g(T)}T=d_{n,g}.
\tag{18.12}
$$

The subspaces in this lower comparison have a strict negative
margin. They contain only finitely many longitudinal frequencies
and angular modes for each fixed $T$. The angular core density
above and longitudinal smoothing therefore approximate them in
the positive form norm by finite sums compactly supported in
$(0,T)\times J$. Finite-dimensional approximation preserves
linear independence and a strict negative margin. After undoing
the gauge, these give actual compact smooth Cartesian functions
on annuli, extended by zero near both axes and the pole. In
particular the supremal density in (18.12) can be approached by
such smooth trial spaces. No assertion that the unrestricted
angular boundary space has finite codimension is needed.

It remains to transfer this density to the original operator.
Put $\ell=\log R$, $f=R^{-1}v$, and use the coordinates (12.3).
Raw measure and direct differentiation give

$$
\begin{aligned}
d\xi&=\tfrac14e^{4\ell}\,d\ell\,da\,d\theta,
&4\|f\|_2^2&=\int e^{2\ell}|v|^2,\\
Zf&=e^{-3\ell}\{2\sin a(\partial_\ell v-v)+4c\partial_av\},
&4\|Zf\|_2^2&=\int e^{-2\ell}
       |2\sin a(\partial_\ell v-v)+4c\partial_av|^2.
\end{aligned}
\tag{18.13}
$$

The integrals on the right are over the log-polar variables.
In (12.12), after the angular gauge and integration in $\ell$,
the cross term involving $-v$ integrates to zero for compact
support or periodic interfaces; its angular-circle part also
has zero real integral. Thus four times the homogeneous
horizontal-minus-potential form is exactly (18.8), including
all magnetic cross terms. The original spectral wall is
$4E\|f\|_2^2=\int E e^{2\ell}|v|^2$.

Write $\omega(a,\theta)=(\sqrt c\cos\theta,\sqrt c\sin\theta,
\sin a/4)\in\Sigma=\{R=1\}$ and
$\delta_r(x,y,z)=(rx,ry,r^2z)$. Complete-field scaling gives

$$
e^{2\ell}M_{n,1}(\delta_{e^\ell}\omega)
       =M_{n,e^{-\ell}}(\omega).
\tag{18.14}
$$

The compact sphere $\Sigma$, including its two axis directions,
is disjoint from the pole. The locally uniform convergence in
Theorem 10.2 and $q_*>0$ imply that for each $\zeta>0$ there is
$\ell_0\ge0$ such that, uniformly in $a,\theta$ and
$\ell\ge\ell_0$,

$$
\frac{g-\zeta}{2\pi}q_n(a)
 \le gM_{n,e^{-\ell}}(\omega(a,\theta))
 \le\frac{g+\zeta}{2\pi}q_n(a).
\tag{18.15}
$$

This is a pointwise comparison of the actual whole marginal,
valid simultaneously for all angular modes. The central term
in (18.13) is nonnegative. On a translate by $a_0\ge0$ of any
fixed finite-dimensional smooth cylinder space its value is at
most $C_{\rm space}e^{-2a_0}\|w\|^2$. The constant is finite by
finite dimensionality and (18.13); the preceding core
approximation also gives finite central derivatives directly.

For the upper index comparison fix $\zeta>0$. Choose real
smooth cutoffs in $\ell$ with squared sum one: one inner cutoff,
and exterior cutoffs spaced by $L$, each supported in an
interval of length $T=L+2h$. Sine and cosine interpolation in
the overlaps of width $h$ gives $\sum_j|\chi_j'|^2\le C/h^2$,
with a constant independent of $L>2h$ and $E$.
The product rule for the actual fields gives the IMS identity

$$
\begin{aligned}
q_1[f]+E\|f\|_2^2
 &=\sum_j\{q_1[\chi_jf]+E\|\chi_jf\|_2^2\}
                          -\int\mathcal I|f|^2\,d\xi,\\
\mathcal I&=\sum_j|\chi_j'|^2
           \left(\frac c{R^2}+\frac{4\sin^2a}{R^4}\right).
\end{aligned}
\tag{18.16}
$$

This is the usual IMS product identity, as in Teschl, Lemma
11.3, printed p.243; here the displayed multiplier follows
from $|\nabla_H\log R|^2=c/R^2$ and
$|Z\log R|^2=4\sin^2a/R^4$. It follows first on the original
smooth core and then on $\mathcal H_1$ by form closure.
The partition is locally finite; the nonnegative energy sums
and the bounded localization multiplier justify the infinite sum.

Allocate $-\mathcal I$ to each localized form using
$\sum\chi_j^2=1$. On exterior supports (18.13) bounds four
times this error by $5C h^{-2}\|w\|^2$. Choose $h$ large
so $5C/h^2\le\zeta q_* /(2\pi)$, and choose the start of the
exterior supports beyond $\ell_0$ in (18.15). Any initial
transition can be included in the fixed inner region. Each
exterior localized original form is consequently bounded below,
after multiplication by four and dropping its central energy, by

$$
\mathcal Q_{g+2\zeta}[w]+\int E e^{2\ell}|w|^2.
\tag{18.17}
$$

The logarithmic endpoints are Dirichlet interfaces. The
localized original form domain maps into this natural homogeneous
domain. On a compact log interval, its cylinder $L^2$ norm is
controlled by the original $L^2$ norm. Approximate first in the
original smooth core, truncate the angular Fourier series, and
apply the angular cutoffs above and longitudinal smoothing.
Identity (12.12) controls convergence in the positive homogeneous
form norm. Passing to the original form closure proves the
inclusion. Only longitudinal interfaces have been introduced.

The inner cutoff is supported in a fixed bounded gauge ball
(for fixed $L,h,\ell_0$). Its Dirichlet original realization,
including its bounded localization error, has compact resolvent.
Indeed (15.9) gives local Euclidean $H^1$ control, (15.11)--(15.12)
give an equivalent shifted form norm, and classical Rellich
compactness on that bounded region gives a compact embedding.
Its strict negative index $K_{\rm in}$ is finite and independent
of $E$. This uses Euclidean control only on that bounded region.

Let $k_+=(g+2\zeta)/(2\pi)$. Since
$\mathcal Q_{g+2\zeta}\ge-k_+\|w\|^2$, an exterior piece starting
at $\ell\ge\tfrac12\log(k_+/E)$ has nonnegative comparison
form (18.17). Only $\log(1/E)/(2L)+O(1)$ pieces can contribute;
each has index at most $D_{g+2\zeta}(L+2h)\le P_{g+2\zeta}(L+2h)$.
The localization map $f\mapsto(\chi_jf)_j$ is injective.
Projection onto the direct sum of local negative spectral
spaces is injective on any strictly negative original subspace:
a vector in its kernel would make every localized comparison
nonnegative, contradicting (18.16)--(18.17).
The strict-index principle therefore gives

$$
\limsup_{E\downarrow0}\frac{N_{n,g}(E)}{\log(1/E)}
 \le\frac{P_{g+2\zeta}(L+2h)}{2L}
 \longrightarrow\frac{d_{n,g+2\zeta}}2\qquad(L\to\infty).
\tag{18.18}
$$

Here $h$ is fixed before $L$ grows, and $E\downarrow0$ is taken
first. The fixed inner index and the finite initial and endpoint
pieces vanish upon division by $\log(1/E)$.

For the lower comparison take $0<\zeta<g-\lambda_n$.
For a fixed $T$, choose an $r$-dimensional compact smooth
cylinder trial space from (18.12), at coupling $g-\zeta$, with
$\mathcal Q_{g-\zeta}[w]\le-\gamma\|w\|^2$ for some $\gamma>0$.
Choose $a_0$ sufficiently large for (18.15) on every interval
$[a_0+jT,a_0+(j+1)T]$, $j\ge0$, and for the central term of
each translated space to be at most $\gamma\|w\|^2/4$.
The latter follows from (18.13)'s bound
$C_{\rm space}e^{-2a_0}$ and decreases on successive translates.
Keep only the intervals for which

$$
E e^{2(a_0+(j+1)T)}\le\gamma/4.
\tag{18.19}
$$

On each copy, four times $q_1+E\|\cdot\|_2^2$ is at most
$(-\gamma+\gamma/4+\gamma/4)\|w\|^2<0$ by (18.15).
After undoing the coordinates these are actual compact smooth
Cartesian trials in the original fixed-noise core. Their
supports are disjoint, so locality makes their direct sum a
strictly negative complex subspace. The number of retained
copies is $\log(1/E)/(2T)+O(1)$, and hence

$$
\liminf_{E\downarrow0}\frac{N_{n,g}(E)}{\log(1/E)}
 \ge\frac r{2T}.
\tag{18.20}
$$

By (18.12) and its smooth-core construction, $r/T$ can approach
$d_{n,g-\zeta}$, with $T$ and the trial space fixed before
$E\downarrow0$. Combining (18.18)--(18.20) gives

$$
\frac{d_{n,g-\zeta}}2
 \le\liminf_{E\downarrow0}\frac{N_{n,g}(E)}{\log(1/E)}
 \le\limsup_{E\downarrow0}\frac{N_{n,g}(E)}{\log(1/E)}
 \le\frac{d_{n,g+2\zeta}}2.
\tag{18.21}
$$

Finally let $\zeta\downarrow0$. Continuity of $d_{n,g}$ and its
strict positivity and finiteness prove (18.3) and continuity of
$L_{n,g}$. The periodic cylinder has been removed through both
index comparisons, while the original source, natural angular
endpoints and full complex $\mathcal H_1$ domain remain fixed.

**Definition 18.3 (attribution and the sharper remainder boundary).**
Theorem 18.2 is a source-specific deduction from Definition
18.1's analytic hypotheses. Its additional mathematical content
is the natural all-mode phase density, its log-interface
comparison and its transfer to the actual positive-noise whole
marginal. The analytic Fredholm theorem is used only for the
bounded polynomial perturbation (18.7), with compactness and
one invertible point verified there. The form-index principle,
product and IMS identities, and Rellich compactness are the
classical intermediates attributed in the proof and in §15.
None of these classical results alone identifies this coefficient
or transfers it to the original retained operator. This
conditional deduction carries no literature-priority claim.

Equation (18.3) answers the limit question (17.27) under the
stated analytic hypotheses. It does not identify the single-trial
supremum $S_{n,g}$ with $L_{n,g}$ or evaluate a numerical
coefficient. No individual eigenvalue law, uniformity in $n$ or
$g$, or physical realization is asserted.
A sharper, separately quantified remainder assertion is

$$
\begin{gathered}
\text{for every integer }n\ge2\text{ and every fixed }g>\lambda_n,
\quad\exists C_{n,g}<\infty,\ \exists E_{n,g}\in(0,1):\\
\left|N_{n,g}(E)-L_{n,g}\log(1/E)\right|\le C_{n,g}
                  \quad(0<E<E_{n,g}).
\end{gathered}
\tag{18.22}
$$

This assertion remains unresolved here. The bounded errors in
the auxiliary periodic count (18.9) do not give (18.22): the
transfer first fixes coupling and interface tolerances and then
takes their limits, without a bounded remainder for the original
count. No replacement of its fixed positive noise, whole
marginal or natural full-domain realization is part of (18.3).

## 追加锚（本行以下为增补区）


## 19. The complete-source error on the full gauge sphere

**Definition 19.1 (the complete marginal error).**
Retain Definition 18.1's analytic assumptions and Definition 10.1's
complete unweighted marginal $M_{n,\epsilon}$. For every integer
$n\ge2$ and $\epsilon\ge0$ define
$e_n(\epsilon)=\sup_{\omega\in\Sigma}|M_{n,\epsilon}(\omega)-M_{n,0}(\omega)|$,
where $\Sigma=\{\rho^4+16z^2=1\}$ includes both axis points.
The uniform small-noise estimate for this quantity, its exterior and
form consequences, and the remaining comparison in (18.22) are given in
[the same-theme continuation, Theorem 20.2 and §§20--21](FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE_GREEN_TAIL.md).

## 追加锚（本行以下为增补区）
