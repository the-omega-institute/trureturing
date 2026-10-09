## 69. A full-reserve gap at fixed unit cable lengths

**Definition 69.1 (the fixed commission and the full reserve).** Use the actual
source, particle measure, collision domain, harmonic calibration and shared field
of Definitions64.5,67.1–67.3 and68.1 in the
[first continuation](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md).
Fix commissioned $a,g>0$, $\Omega\ge1$, $\nu=0$ and $0<\delta\le1$ for the
entire commission, and fix either complete prescription
$\diamond\in\{\mathrm c,\mathrm k\}$ separately. These commissioned parameters
are distinct from the original actor's parameters. Every intrinsic cable length
and conductance is one. The parameter $\delta$ is the storage density in
(64.6), not a cable length, tube radius or mesh spacing.

For an authentic nonempty installed source $D$, write

$$
\begin{aligned}
X_D&=\mathcal K_D\otimes\mathcal F_H\otimes\mathcal A,\\
\mathcal E_D
 &=\operatorname{Dom}(A_D^{1/2}\otimes I)
   \cap\operatorname{Dom}(I\otimes\mathsf n^{1/2}),\\
P_D&=(W_DW_D^*)\otimes I,\qquad Q_D=I-P_D,\\
\mathfrak f_D[z]&=\Omega\|(I\otimes h_D^{1/2}\otimes I)z\|^2.
\end{aligned}
\tag{69.1}
$$

The auxiliary Hilbert space $\mathcal A$ is any nonzero supplied space. The form
$q_D$ is exactly (67.5) at zero charge, hence on this intersection

$$
q_D[z]=\|(A_D^{1/2}\otimes I)z\|^2
-g\left\langle z,\left(\sum_{p\in D}\phi(p)m_p\otimes I\right)z\right\rangle
+\mathfrak f_D[z].
\tag{69.2}
$$

In particular the reference has its actual field form. Both complete Green
prescriptions retain their own actual $h_D$ and every bank mode and spectator;
zero charge makes the pair, linear and compensation coefficients zero. It does
not replace either prescription or remove its field.

The particle part of $\mathcal E_D$ is the full Hilbert-valued domain of
Definition64.5: one-particle atoms and intervals, two-particle distinct atomic
pairs, both orders of mixed atom/cable slices, distinct-cable rectangles and both
triangles of every same-cable square. Exchange symmetry, slice/cell boundary
matching, port endpoints, grounded endpoints and both collision traces are part
of this domain, including shared-port collisions. No cell-corner value of a
general $H^1$ function is stipulated. The singleton's continuum two-particle
space is included. All tensor norms retain unknown field/auxiliary correlations;
no uniform number-moment cutoff is imposed beyond membership in
$\mathcal E_D$.

**Theorem 69.2 (source-uniform gap on the actual reserve intersection).** For
every $z\in\mathcal E_D\cap Q_DX_D$,

$$
q_D[z]\ge
\left(\frac{a}{9\delta}-2g\right)\|z\|^2+\mathfrak f_D[z]
\ge\left(\frac{a}{9\delta}-2g\right)\|z\|^2.
\tag{69.3}
$$

The constant is independent of the source, fixed cap, bank and auxiliary sizes,
$\Omega\ge1$ and the input's field moments. The restriction is the closed form
restriction supplied by Lemma68.2; no self-adjoint operator compression is an
additional hypothesis.

**Proof.** Work first in particle sector $N=1$ or $N=2$, with all retained
field/auxiliary coefficients. Let $R_N$ be the atomic restriction of
Lemma64.5b and $E_N$ the kinetic minimizing lift of Theorem64.6, tensored with
identity on those coefficients. For $u=R_Nz$, put

$$
v=z-E_Nu.
\tag{69.4}
$$

The identities $R_NE_N=I$ and $\operatorname{Ran}E_N=
\operatorname{Ran}W_N$ give $R_Nv=0$ and $Q_Dv=z$. The minimizing property of
$E_N$ gives kinetic-form orthogonality to every zero-atomic vector, so

$$
k_{\delta,N}(z)=k_{\delta,N}(E_Nu)+k_{\delta,N}(v)
\ge k_{\delta,N}(v).
\tag{69.5}
$$

Apply the full zero-atomic estimate (64.9) to $v$, then use that $Q_D$ is an
orthogonal projection:

$$
\|z\|^2=\|Q_Dv\|^2\le\|v\|^2
\le9\delta\,k_{\delta,N}(v)
\le9\delta\,k_{\delta,N}(z).
\tag{69.6}
$$

Here $z$ need not have zero atomic data. The zero-atomic vector is $v$ in
(69.4), not an identification of $Q_DX_D$ with $\ker R_N$.

All these operations preserve the stated intersection. Indeed $R_N$ is a
bounded restriction to mass-one atomic coordinates, $E_N$ has finite particle
operator-domain range and both commute with the number operator. Subtraction
preserves every Hilbert-valued linear trace condition. The minimizing
orthogonality and (64.9) extend to Hilbert-valued coefficients by tensoring their
quadratic-form inequalities with identity, or by finite coefficient projections
and form-norm limits. This does not bound or discard a field excitation.
The estimate (64.9) already includes mixed slices, rectangles, both dissected
triangles and all their ground/collision traces; these are the same domains
used in (69.4)–(69.6).

On a singleton $R_2$ has zero target and $E_2=W_2=0$. Thus $Q_2=I$ on its
nonzero continuum sector, and the same argument uses $v=z$. On the reference
$W_D=I$, so a reserve has zero reference component. Summing the two particle
sector inequalities therefore gives
$\|(A_D^{1/2}\otimes I)z\|^2\ge a\|z\|^2/(9\delta)$ on the entire reserve.
Finally $0\le\sum_p\phi(p)m_p\le2I$ on every stratum, and
$\mathfrak f_D\ge0$. Substitution in (69.2) proves (69.3). $\square$

## 70. Matching joint depth and storage-density control for the unchanged recurrence

**Definition 70.1 (full-input and legal-history infima).** Let
$\mathfrak h=(D_0,\ldots,D_n)$ be an authentic finite accepted Left/Right graft
prefix of Definition68.1. It has one immutable INITIAL and one fixed cap $H$;
all complete supplied contexts, whole candidates and original guards are
retained. Original Reads and refusals may intervene, with their actual responses
and acquired records, but are not counted in $n$. There is no accepted whole-rho
step in this prefix and no service after original Stop.

Let $Y_{\mathfrak h,n}$, $\boldsymbol q_{\mathfrak h,n}$, $V_j$, $B_{j,n}$ and
$\mathcal R_j$ be exactly (68.2)–(68.5). In particular the recurrence is (68.2),
with each actual old/new branch diagonal and every historical cross form. Its
full domain, supplied by Theorem68.3, is

$$
\mathscr E_{\mathfrak h,n}
=\mathcal E_{D_n}\oplus\bigoplus_{j<n}
 (\mathcal E_{D_j}\cap Q_jX_j).
\tag{70.1}
$$

This direct-sum notation factors the same $\mathcal F_H\otimes\mathcal A$
only once. For $y=(b,z_{n-1},\ldots,z_0)$ in this domain define the actual
nonnegative branch field contribution

$$
\mathfrak F_{\mathfrak h,n}[y]
=\mathfrak f_{D_n}[b]+\sum_{j<n}\mathfrak f_{D_j}[z_j].
\tag{70.2}
$$

Each summand uses its branch's actual $h_{D_j}$ on the one bank; this notation
does not identify old and new field matrices.

At fixed $a,g,\Omega,\delta,\diamond$ and nonzero $\mathcal A$, set

$$
\begin{aligned}
e_{\mathfrak h}^{\diamond}(n,\delta)
 &=\inf\{\boldsymbol q_{\mathfrak h,n}[y]:
          y\in\mathscr E_{\mathfrak h,n},\ \|y\|=1\},\\
e^{\diamond}(n,\delta)
 &=\inf_{\mathfrak h\in\mathscr H_n}
           e_{\mathfrak h}^{\diamond}(n,\delta),\\
M(n,\delta)&=\min\{n\delta^2,\sqrt{n\delta}\}.
\end{aligned}
\tag{70.3}
$$

Here $\mathscr H_n$ ranges over actual length-$n$ prefixes at arbitrary finite
caps, each cap fixed within its own run, with arbitrary authentic INITIAL and
complete legal contexts. These are infima over mathematical form inputs,
separately from the choice of legal history. They are not infima over natively
preparable or reachable states. The notation suppresses the fixed commissioned
parameters; common and killed infima are separate quantities.

**Theorem 70.2 (all-input joint lower bound).** For all commissioned $a,g>0$,
put

$$
R=4000(a+g),\qquad
C=\max\left\{\frac{9R^2}{a},R\right\}.
\tag{70.4}
$$

For every $n\ge0$, $0<\delta\le1$, $\Omega\ge1$, either separate prescription,
every $\mathfrak h\in\mathscr H_n$ and every full form input $y$,

$$
\boldsymbol q_{\mathfrak h,n}[y]
\ge\mathfrak F_{\mathfrak h,n}[y]
       -\bigl(2g+C M(n,\delta)\bigr)\|y\|^2.
\tag{70.5}
$$

Consequently $e_{\mathfrak h}^{\diamond}(n,\delta)$ and
$e^{\diamond}(n,\delta)$ are at least $-2g-C M(n,\delta)$.
The constant has no dependence on history, source, cap, bank or auxiliary size,
$\Omega$ or field moments.

**Proof.** Reuse the exact full-domain expansion in Theorem68.3 and the bounded
cross form in Lemma68.2; no history term is changed. Its residual coefficient
$r$ from (68.4) obeys a bound uniform in density. Indeed

$$
\beta_1\le2\sqrt\delta,\qquad
\beta_2\le16\sqrt\delta,\qquad
0\le s_N\le\beta_N^2/2.
\tag{70.6}
$$

For the second inequality use
$\sqrt{3\delta+9\delta^2/4}\le(5/2)\sqrt\delta$ and
$9\sqrt2\,\delta\le(27/2)\sqrt\delta$.
Inserting these in the supplier's residual formula gives

$$
r_1\le(21a+11g/2)\sqrt\delta,\qquad
r_2\le(3282a+576g)\sqrt\delta,
\qquad r\le R\sqrt\delta.
\tag{70.7}
$$

Here $\delta\le\sqrt\delta$ has been used only in an estimate, not in a
change to any kinetic coefficient.

Write $u=\|b\|$ and $v=(\sum_{j<n}\|z_j\|^2)^{1/2}$. The active diagonal
is bounded below by $-2g\|b\|^2+\mathfrak f_{D_n}[b]$.
Apply Theorem69.2 to every actual reserve. Since each $B_{j,n}$ is a contraction,
(68.3), Cauchy–Schwarz and (70.7) bound the entire cross sum below by
$-2R\sqrt{n\delta}\,uv$. Thus

$$
\boldsymbol q_{\mathfrak h,n}[y]
\ge\mathfrak F_{\mathfrak h,n}[y]-2g\|y\|^2
 +h v^2-2tuv,
\qquad h=\frac a{9\delta},\quad t=R\sqrt{n\delta}.
\tag{70.8}
$$

The field cross term vanishes within each old branch by the full tensor-space
orthogonality of Lemma68.2. Its diagonal in (70.8) is still (70.2), including
arbitrary reference/field/auxiliary correlations. No equality between
$h_{D_j}$ and $h_{D_{j+1}}$ or moment estimate is involved.

For completeness, the elementary two-variable minimization here has loss

$$
L_-(n,\delta)
=\frac{\sqrt{h^2+4t^2}-h}{2},\qquad
hv^2-2tuv\ge-L_-(u^2+v^2).
\tag{70.9}
$$

This follows by diagonalizing the real matrix with entries
$\left(\begin{smallmatrix}0&-t\\-t&h\end{smallmatrix}\right)$.
The identity $L_-(h+L_-)=t^2$ gives

$$
L_-\le\min\left\{\frac{t^2}{h},t\right\}
=\min\left\{\frac{9R^2}{a}n\delta^2,
                 R\sqrt{n\delta}\right\}
\le C M(n,\delta).
\tag{70.10}
$$

The scalar calculation is only an estimate on the already existing form;
$h$ is not an installed reserve stiffness or energy shift. Combining
(70.8)–(70.10) proves the result, with $t=L_-=0$ when $n=0$. $\square$

**Theorem 70.3 (one legal history and one normalized matching state).** Suppose

$$
0<g<a\lambda,\qquad \lambda=3-2\sqrt2,\qquad
\mu=a\lambda-g>0.
\tag{70.11}
$$

Set

$$
\kappa=\frac{2\sqrt2}{75}\mu,\qquad
B=\frac{525}{2}a,\qquad
c=\frac12\min\left\{\frac{\kappa^2}{B},\kappa\right\}>0.
\tag{70.12}
$$

For every $n\ge1$, $0<\delta\le1$ and $\Omega\ge1$, there is an authentic
INITIAL-$\alpha$ length-$n$ history at one fixed cap and a single normalized
$\Psi\in\mathscr E_{\mathfrak h,n}$ such that, for either separate prescription,

$$
\boldsymbol q_{\mathfrak h,n}[\Psi]
\le6a-cM(n,\delta).
\tag{70.13}
$$

The constants depend only on the displayed commissioned $a,g$. In particular

$$
-2g-CM(n,\delta)\le e^{\diamond}(n,\delta)
\le6a-cM(n,\delta)
\tag{70.14}
$$

in this regime. The upper statement is an existence statement for a legal
family, not an upper estimate for every prescribed history or every input.

**Proof.** Use the authentic source family of Theorem68.6, including its
Left/Right alternatives, without changing its acquisition or source laws.
Explicitly, fix $H=n+1$ at the start, put $t_0=\alpha$, and choose any fixed
word of $n$ Left/Right directions. At step $j$ supply the complete named
one-leaf context $\alpha$ and take

$$
t_{j+1}=\begin{cases}
\langle\alpha,t_j\rangle,&\mathrm{Left},\\
\langle t_j,\alpha\rangle,&\mathrm{Right}.
\end{cases}
\tag{70.15}
$$

The original whole-candidate guard is exactly the one of PR57 §57.1 and
TheoremPR57.T2 in
[Transport Memory Completion](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#571-the-unchanged-source-and-the-exact-target).
The complete candidate has $j+2\le H$ leaves, so all $n$ calls are accepted,
including the final equality case. Every added occurrence is distinct; all
labels, brackets and left/right order remain those of (70.15). The immutable
INITIAL remains $\alpha$, rather than the current $t_j$.
Original checkpoint Reads return the actual $E(t_j)=A^{j+1}$ in the pinned
Clifford algebra. If requested after the prefix, one further alpha graft is
refused at $H+1$ leaves, preserves $t_n$ and supplies no candidate Read; a
subsequent original Read and Stop have their original meanings. No event is
placed after Stop. The prescribed calls depend only on public inputs.

Let $p_0=o$ be the initial occurrence, and let $p_{j+1}=Rp_j$ for Left and
$p_{j+1}=Lp_j$ for Right. Then $f_j=e_{p_j}$ is a unit discrete
one-particle vector with $f_{j+1}=\iota_jf_j$. At each actual $D_j$, use exactly
the nonzero normalized reserve $w_j$ constructed in (68.10), for this $f_j$.
The supplied estimates (68.11), with $\gamma=1+3\delta/2\le5/2$, imply

$$
\begin{aligned}
q_{D_j}(W_jf_j,w_j)&\le-k_*,&
k_*&\ge\kappa\sqrt\delta,\\
q_{D_j}[w_j]&\le6a+\frac B\delta,&
q_{D_n}[W_nf_n]&\le6a.
\end{aligned}
\tag{70.16}
$$

These are the particle estimates, or equivalently their full forms on the
single shared vacuum. They use every actual degree and current-root
one-body field; the old root's changed degree and its relocated field values
are not replaced by a compression identity. The same normalized reserve
supplies its coupling and energy bound, as in Lemma68.5.

Fix the complete bank $\mathcal F_H$ once for the run and let $|0_H\rangle$
be its one canonical vacuum. By (67.3), every actual $h_{D_j}$, common or killed
as separately chosen, annihilates this same vector, including all spectator
modes. Choose one unit $\xi\in\mathcal A$. For $x,y\ge0$ with $x^2+y^2=1$,
form the single vector

$$
\Psi(x,y)=
\left(xW_nf_n,\frac y{\sqrt n}w_{n-1},\ldots,
                    \frac y{\sqrt n}w_0\right)
\otimes|0_H\rangle\otimes\xi.
\tag{70.17}
$$

Its full squared norm is $x^2+y^2$ by branch orthogonality. Each component is
in its actual form domain, and the same vacuum is in the common number-form
domain, so this one finite direct-sum state is admissible. The factorization
in (70.17) creates no separate field copies or successive re-preparations.

For this active input (68.5) gives
$B_{j,n}(xW_nf_n)=xW_jf_j$ for all $j$ simultaneously. Consequently the exact
history expansion, with every old cross term and actual diagonal, gives

$$
\begin{aligned}
\boldsymbol q_{\mathfrak h,n}[\Psi(x,y)]
&\le6ax^2+\left(6a+\frac B\delta\right)y^2
             -2\kappa\sqrt{n\delta}\,xy\\
&=6a+\frac B\delta y^2-2\kappa\sqrt{n\delta}\,xy.
\end{aligned}
\tag{70.18}
$$

Optimize only these two weights of the already simultaneous state. Put

$$
\begin{aligned}
h_+&=B/\delta,&t_+&=\kappa\sqrt{n\delta},\\
L_+&=\frac{\sqrt{h_+^2+4t_+^2}-h_+}{2},&
x&=\frac{t_+}{\sqrt{t_+^2+L_+^2}},\qquad
y=\frac{L_+}{\sqrt{t_+^2+L_+^2}}.
\end{aligned}
\tag{70.19}
$$

Both weights are positive. Since $L_+(h_++L_+)=t_+^2$, they satisfy
$x^2+y^2=1$ and $h_+y^2-2t_+xy=-L_+$. Rationalizing the same expression yields

$$
L_+=\frac{2t_+^2}{\sqrt{h_+^2+4t_+^2}+h_+}
\ge\frac12\min\left\{\frac{t_+^2}{h_+},t_+\right\}.
\tag{70.20}
$$

Indeed if $t_+\le h_+$ the denominator is at most
$(\sqrt5+1)h_+\le4h_+$; if $t_+\ge h_+$ it is at most
$(\sqrt5+1)t_+\le4t_+$. Hence

$$
L_+\ge\frac12\min\left\{\frac{\kappa^2}{B}n\delta^2,
                          \kappa\sqrt{n\delta}\right\}
\ge cM(n,\delta).
\tag{70.21}
$$

Equations(70.18)–(70.21) prove (70.13). All unused reference, two-particle,
mixed/cell, field-excitation and auxiliary sectors stay in the carrier; only
this chosen state has zero amplitude in them. The field is one complete bank
with $2^H-1$ modes, not an optimized component for each branch. No part of
this variational argument is a native preparation or reachability assertion.
The lower half of (70.14) is Theorem70.2; the upper half takes the infimum over
histories after constructing this one legal history and this one normalized
state. For $n=0$, the corresponding upper bound $e^{\diamond}(0,\delta)\le6a$
follows from the initial one-leaf calibrated state with the same vacuum.
$\square$

## 71. Uniform mathematical floors across separately legal commissions

**Theorem 71.1 (the exact density criterion in the matching regime).** Fix
commissioned $a,g>0$ and one separate prescription $\diamond$. Let
$(n_k,\delta_k,\Omega_k)$ be any sequence with $n_k\in\mathbb N_0$,
$0<\delta_k\le1$ and $\Omega_k\ge1$. The density and frequency are fixed
within each individual commission. Say that this sequence has a uniform full
mathematical floor if a finite constant $L$ bounds
$\boldsymbol q_{\mathfrak h,n_k}[y]\ge L\|y\|^2$ for every $k$, every separately
legal history $\mathfrak h\in\mathscr H_{n_k}$ and every full form input.

For all such $a,g$, a sufficient condition is

$$
\sup_k n_k\delta_k^2<\infty.
\tag{71.1}
$$

If $0<g<a(3-2\sqrt2)$, this condition is also necessary for that all-history,
all-form-input floor. The constants are uniform in $\Omega_k$, caps, sources,
bank and auxiliary sizes and input field moments. Necessity is not asserted
outside this matching parameter regime, or for a single selected history
sequence with a restricted input class.

**Proof.** Put $u_k=n_k\delta_k^2$ and $v_k=\sqrt{n_k\delta_k}$.
Since $0<\delta_k\le1$,

$$
u_k\le v_k^2,\qquad
\min\{u_k,\sqrt{u_k}\}\le M(n_k,\delta_k)\le u_k.
\tag{71.2}
$$

Thus bounded $u_k$ gives a common floor
$-2g-C\sup_k u_k$ by Theorem70.2, even with the actual nonnegative field
contribution retained. Conversely, unbounded $u_k$ has a subsequence tending
to infinity; (71.2) makes $M$ tend to infinity on that subsequence. In the
matching regime Theorem70.3 supplies, at each of these indices, one actual
INITIAL-$\alpha$ history with fixed cap $n_k+1$ and one normalized full state
whose energy is at most $6a-cM(n_k,\delta_k)$, tending to minus infinity.
This contradicts a floor over all those histories and states.
The argument uses no within-run change of $\delta_k$ and no infinite fixed-cap
history. In a single fixed-cap run every accepted nonempty graft adds at least
one leaf, hence $n\le H-\operatorname{leaves}(\mathrm{INITIAL})$ as in
Theorem68.6; its finite-history floor remains finite. $\square$

**Assumption 71.2 (scope of realization and correspondence).** A spatial or
native interpretation of these mathematical forms requires the complete
additional hypotheses of Definition68.7, with its cited Definitions66.10 and
67.11, unchanged. In particular the original source includes every literal
label, bracket, order and distinct occurrence, immutable INITIAL, original
source-independent actor initialization, complete contexts and candidates,
whole-candidate guards, accepts/refusals, original Read, absorbing Stop and
all actually acquired records. The original actor's arbitrary, unbounded or
possibly zero $a$, untagged radius-$7/25$ $b$, destructive operations and joint
history-dependent errors are not replaced by the commissioned positive
parameters in (69.1).

Unknown-state ingress, recovery, original Read/Stop and operation correspondence,
full-domain dynamics, reference and clock calibration, harmonic/projection
control, complement retention and cross-block control are separate hypotheses.
An encoded or alternative carrier requires their actual correspondence, not
only a Hilbert-space isomorphism, source copy, static Green response or
calibrated-state re-preparation. Proposition66.8 and the nonintertwining
boundary of Proposition68.4 remain applicable.

A spatial interpretation additionally requires the operation/metric bridge,
an isotropic local physical mediator for both complete pair laws, and the
packing, transverse, exterior, leakage and collision hypotheses named in
Definition68.7. The conditional incidence transports66.9/67.9 supply no such
mediator. There is no spatial dimension parameter in $M(n,\delta)$.
Changing $\delta$ between separately legal commissions supplies neither a
native control operation nor acquisition, reset or within-run update rights.

Every original acquisition premise, the separate paid archive/nonadvancing-cut
premises and the full-tail once-sampled Read premises cited in68.7 retain their
own sources and domains. Every construction, preparation, field/compensation/
stiffness installation, control, service, production, storage, hold, retention,
maintenance, precision and total lifetime price remains an additional
hypothesis. A literal-budget theorem for another source is not a certificate
for this carrier's prices. A mathematical floor or its failure is not a price
law, physical instability assertion or spatial-three theorem.

The analytic suppliers have exactly their existing scope: Teschl,
[*Mathematical Methods in Quantum Mechanics*](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf),
Theorems2.13 and6.24, provides closed-form representation and KLMN; the finite
bounded block perturbation is already used in Theorem68.3.
Bolte–Kerner, [arXiv:1207.5648v1](https://arxiv.org/pdf/1207.5648v1),
Definition3.1/Proposition3.2, supplies its stated Lebesgue-product metric-graph
trace framework. The atomic/mixed form domains used here remain precisely
Definition64.5, not an extension attributed to that supplier. Neither citation
supplies arbitrary $H^1$ corner traces or the native/spatial correspondence
hypotheses above.

## 71.99 追加锚（本行以下为增补区）

## 72. Exact unit cables and the full fixed-source free one-particle limit

**Definition 72.1 (fixed data and the extent of the assertion).** Fix an
actual nonempty finite full binary source $D$, with its actual occurrences,
inherited seams and two distinct grounded stubs at each current leaf, exactly
as in Definition64.5 of the
[first continuation](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md).
Write $n=|D|$. Fix commissioned $a>0$, $0<\delta\le1$, an integer ambient
dimension $s\ge3$, and a positive number $m_g$ for each distinct grounded
endpoint $g$. All these data are fixed as $\varepsilon\downarrow0$.
The number $n$ is source cardinality, not ambient dimension. Put

$$
 t=\varepsilon^{1/s},\qquad r=t^{s-1}
   =\varepsilon^{(s-1)/s},\qquad
 \rho=\omega_{s-1}^{-1/(s-1)},
 \tag{72.1}
$$

where $\omega_{s-1}$ is the volume of the unit ball in
$\mathbb R^{s-1}$. A circular cylinder of radius $\rho\varepsilon$ has
cross-sectional measure $\varepsilon^{s-1}$. Reference chamber volumes are
$m_p=1/\delta$ at source ports and the prescribed $m_g$ at ground vertices.
These are volume-to-cross-section ratios. They are not additional source
coordinates or a physical apparatus-mass assertion.

The assertion below concerns only the free kinetic operator
$L:=A_{\delta,D,1}$, associated with $a k_{\delta,1}$, on the entire
one-particle Hilbert space of Definition64.5. It does not replace that space
by its harmonic subspace. It constructs Euclidean domains and a generalized
norm-resolvent relation for fixed nonreal compact spectral sets. The mature
convergence theorem used is Cherednichenko–Ershova–Kiselev,
[*Norm-resolvent convergence for Neumann Laplacians on manifolds thinning to
graphs*, arXiv:2205.04397v4](https://arxiv.org/html/2205.04397v4),
Section2, Section3 and Theorem4.5. Its ambient dimension $d$ is denoted here
by $s$. The geometry and the source-specific identifications below are
ordinary deductions for the present source; the cited convergence theory is
prior theory, not a new theorem attributed to this construction.

**Proposition 72.2 (the complete target norm and its massive-port operator).**
Use an orientation of each of the $2n$ unit cables, and write
$F=(f,(u_e)_e)$. Then the exact target Hilbert space, form domain and form are

$$
\begin{aligned}
\mathcal H_\delta
 &=\mathbb C^D\oplus\bigoplus_{e\in\mathcal E_D}L^2((0,1),\delta\,dx),\\
\|F\|_\delta^2
 &=\sum_{p\in D}|f_p|^2+\delta\sum_e\int_0^1|u_e(x)|^2\,dx,\\
\mathcal Q_\delta
 &=\{F:u_e\in H^1(0,1),\ u_e(p)=f_p
       \text{ at each source end},\ u_e(g)=0
       \text{ at each ground end}\},\\
\ell[F,V]&=a\sum_e\int_0^1u'_e\overline{v'_e}\,dx.
\end{aligned}
\tag{72.2}
$$

The atomic and cable coordinates in $\mathcal H_\delta$ are independent;
endpoint matching is a domain condition. Define the derivative directed
from an endpoint into its cable by
$\partial_{\rm in}u_e=u'_e(0)$ at its initial end and
$\partial_{\rm in}u_e=-u'_e(1)$ at its terminal end. The represented operator
has precisely the domain and action

$$
\begin{aligned}
\operatorname{Dom}L
 &=\{F\in\mathcal Q_\delta:u_e\in H^2(0,1)\text{ for every }e\},\\
(LF)_e&=-\frac a\delta u''_e,\qquad
(LF)_p=-a\sum_{e\sim p}\partial_{\rm in}u_e(p).
\end{aligned}
\tag{72.3}
$$

There is no additional zero-flux condition at a massive source port.
There is no ground atomic coordinate.

**Proof.** Formula(72.2) is Definition64.5's measure and one-coordinate
kinetic form, with no omitted interval. Integration by parts gives the
interior term $-a u''_e$ and the endpoint term
$-a\partial_{\rm in}u_e(p)\overline{f_p^V}$ at a source port.
The Hilbert norm has cable density $\delta$ and atomic mass one, giving
exactly (72.3). Conversely these terms represent the form for every test
in $\mathcal Q_\delta$. Testing on compactly supported cable functions
shows that membership in the operator domain forces $u''_e\in L^2$;
in one dimension this gives $H^2$. The remaining tests determine the
atomic output and impose no extra equation on its flux. At grounded ends
the test trace is zero. Closed-form representation, used in64.5a, supplies
self-adjointness; no multidimensional corner regularity enters this
calculation. $\square$

**Proposition 72.3 (a separated straight skeleton in every $s\ge3$).**
The half source tree admits a straight unit-edge embedding in
$\mathbb R^3$ such that every source vertex has height in $(1/4,3/4)$,
every ground endpoint has height zero, all ground endpoints are distinct,
and segments meet only at their prescribed common endpoints. Incident
rays have a positive minimum angle and nonincident compact segments and
vertices have positive clearance. Reflection in the height-zero plane
produces a connected embedded double with $3n+1$ vertices, $4n$ unit
edges and no self-loops. The same assertion holds in $\mathbb R^s$ by
using a fixed three-dimensional linear subspace.

**Proof.** Place the root at height $1/2$. Install inherited tree edges
successively. Choose each unit direction in the open band with vertical
component of absolute value less than $1/(8(n+1))$. All source vertices
then have heights in $(3/8,5/8)$. The directions for a new segment from
$p$ which meet an already installed segment not incident to $p$ form a
set of spherical area zero: they are radial projections from $p$ of a
line segment, hence at most one-dimensional. Passing through an existing
vertex, coinciding with a previous incident ray, and placing a coincident
endpoint likewise exclude sets of area zero. Finitely many such exclusions
cannot exhaust the band. Induction gives the embedded source tree.

For a ground stub from a leaf $p$, its possible unit-distance endpoints
on the plane form a circle with radius $\sqrt{1-p_3^2}$. The union of the
corresponding segments is a right circular cone truncated at the plane.
A fixed straight segment intersects this cone in at most two points unless
its supporting line lies on the cone. A line contained in this cone is a
generator, which excludes only one azimuth. An incident segment at $p$
also excludes at most its own generator. Thus finitely many existing
segments exclude finitely many azimuths. Excluding previously chosen
ground endpoints and repeated rays leaves a choice for each of the two
distinct stubs. Every stub is strictly above the plane except at its
ground endpoint. This also proves separation from the reflected open
half. Finiteness now gives the asserted clearance and angle margins.

A full binary source has $n-1$ seams and $n+1$ ground stubs. The double
has two copies of the $n$ source vertices, one vertex at each of the
$n+1$ grounds, and two copies of all $2n$ cables. Reflection introduces
ordinary cycles but no edge from a vertex to itself. No cycle-length
placement equation is required, because the second half is the reflection
of the first. All three-dimensional distances remain the same in the
higher-dimensional embedding. $\square$

**Definition 72.4 (truncated conical chambers with exact volume).**
Choose once a sufficiently small $0<\alpha<\pi/4$, using the angle and
clearance margins of72.3. Angular caps of radius $2\alpha$ about different
incident rays at a vertex are disjoint. At a ground vertex use both its
upper ray and its reflection; their caps avoid the equator. Set
$q=\rho\tan\alpha$.

For degree $k$ and reference volume $m_v$, start with a radial body about
zero. Outside these caps its radial function is $R_v$. In polar angle
$\theta$ about each incident axis, set it equal to
$R_v\sec(\alpha-\theta)$ near $\theta=0$, and join smoothly to $R_v$
within the cap, with identical fixed transition profiles at every port.
This is a conical tip with apex $c_v d$, where $d$ is its unit axis and
$c_v=R_v\sec\alpha$. Choose $R_v>0$ so that the untruncated body's
volume is $m_v$. The volume coefficient depends only on $s,k,\alpha$
and the transition profile, since the caps are disjoint; in particular
$R_v$ and $c_v$ do not depend on their actual directions.

Truncate each tip by the plane with axial coordinate $c_v-qt$. For all
small $t$ this cuts within the exact cone. Its plate is an
$(s-1)$-disk of radius $\rho t$ and measure $t^{s-1}$. Each removed cone
has volume $qt^s/s$. Denote the truncated radial function by
$F^{\rm tr}_{v,t}$. Choose a nonnegative smooth spherical function
$\psi_v$ supported away from all the port caps, with
$\int_{\mathbb S^{s-1}}\psi_v\,d\omega=1$, and set

$$
 F_{v,t}(\omega)^s
   =F^{\rm tr}_{v,t}(\omega)^s+kqt^s\psi_v(\omega),\qquad
 K_v(t)=\{\lambda\omega:0\le\lambda<F_{v,t}(\omega)\}.
 \tag{72.4}
$$

For a ground chamber choose the profiles reflection-even and choose
$\psi_v$ even and supported away from the equator. The supports can be
fixed away from slightly enlarged caps of the initial directions, so
small subsequent changes of directions preserve all these conditions.
In particular the chamber remains spherical near the equator.

**Proposition 72.5 (reference correspondence and exact Euclidean assembly).**
The construction72.4 and a perturbation of the skeleton give domains
$\Omega_\varepsilon\subset\mathbb R^s$ with the following properties.
Every physical edge is a straight circular cylinder of length exactly one
and cross-sectional measure $\varepsilon^{s-1}$. Its two full plates
match its two chambers. The chambers have precisely the volumes

$$
 |Q_v^\varepsilon|=m_v\varepsilon^{s-1},\qquad
 Q_v^\varepsilon=b_v^\varepsilon+rK_v(t).
 \tag{72.5}
$$

Their open interiors are pairwise disjoint, and every chamber-cylinder
closure intersection is exactly the prescribed plate. There are no other
intersections. Each chamber has smooth noncontact boundary and flat
contact plates meeting it at the fixed interior angle $\pi-\alpha<\pi$.
The assembled exterior is Lipschitz, allowing its dihedral rims.
The double is invariant under the reflection
$\mathcal R(x_1,x_2,x_3,x_4,\ldots)=(x_1,x_2,-x_3,x_4,\ldots)$.
The plane $x_3=0$ meets only ground chambers, in equatorial disks, and
meets their exterior orthogonally. The open upper half is connected and
Lipschitz.

For every vertex there is a fixed reference ball $Q_v^0$, of volume
$m_v$ and containing zero, and a volume-preserving homeomorphism
$\mathcal T_v^\varepsilon:Q_v^0\longrightarrow K_v(t)$ such that

$$
 Q_v^\varepsilon
 =\varepsilon^{(s-1)/s}\mathcal T_v^\varepsilon(Q_v^0)
       +b_v^\varepsilon.
 \tag{72.6}
$$

Thus the reference volume in equation(1) of the cited paper is exactly
$m_v$, rather than merely comparable with it.

**Proof.** Radial integration gives
$|K_v(t)|=s^{-1}\int F_{v,t}^s=m_v$, since the correction in(72.4)
restores precisely $kqt^s/s$. The untruncated tip's meridian is the line
$z=c_v-y\tan\alpha$. Its truncation at $z=c_v-qt$ has radius
$qt/\tan\alpha=\rho t$ and interior angle $\pi-\alpha$.
Compensation takes place away from this entire conical neighbourhood.

In physical coordinates each plate is at distance

$$
 h_v(\varepsilon)=rc_v-q\varepsilon
 \tag{72.7}
$$

from its chamber centre. Give every required centre pair $v,w$ the
distance $L_{vw}=1+h_v+h_w$. Keep the root position and the previously
chosen direction of each inherited edge, and place source centres
recursively using these distances. For a ground neighbour $g$ of leaf
$p$, keep its originally chosen horizontal unit azimuth $a_g$ and set

$$
 b_g^\varepsilon
  =(b_p^\varepsilon)_{\rm hor}
   +\sqrt{L_{pg}^2-(b_p^\varepsilon)_3^2}\,a_g,
 \qquad (b_g^\varepsilon)_3=0.
 \tag{72.8}
$$

The square root is positive for small $\varepsilon$. All centres and
incident directions converge to those in72.3. Orient each port along its
actual centre line. The disk centres are on that line and the distance
between their planes is $L_{vw}-h_v-h_w=1$, with no length error.
The physical plate radius is $r\rho t=\rho\varepsilon$.

Nonincident compact pieces retain their positive separation after this
small perturbation and attachment of bodies of diameter $O(r)$.
Near a common centre the disjoint angular caps separate incident
attachments. In the conical collar, truncation confines the retained
chamber to the inward half-space of the plate, while the cylinder interior
lies in the outward half-space; locally their closures meet exactly at the plate.
Away from this collar, the finite angular separation and
$\varepsilon/r=t\to0$ separate the cylinder from all other chamber
parts and incident cylinders. These observations cover both local
incident pairs and all nonincident pairs. Reflecting completes the
double. Explicitly take
$\Omega_\varepsilon=\operatorname{int}(\bigcup_e\overline{Q_e^\varepsilon}
\cup\bigcup_v\overline{Q_v^\varepsilon})$, with both reflected halves
and each ground chamber included once. At an interior point of a matching
plate the union contains a neighbourhood, so these attachments make an
open connected domain. Near the grounding plane the ground chamber is
spherical and no other piece reaches the plane, proving the cut geometry.
The flat/conical rims have fixed nonzero angles, so their neighbourhoods
are Lipschitz. No assertion of global $H^2$ regularity follows.

For completeness, volume equality can be strengthened to the
volume-preserving reference homeomorphism in(72.6). Let the reference
ball have radius $R_0$, so $|\mathbb S^{s-1}|R_0^s=sm_v$.
Transport the positive continuous spherical density $R_0^s\,d\omega$
to $F_{v,t}^s\,d\omega$ by a homeomorphism $h$ of the sphere. One
explicit construction uses successive marginal and conditional
cumulative distributions in latitude coordinates. Each interior
conditional density is positive, so its cumulative distribution has a
continuous strictly increasing inverse. Induction on sphere dimension
constructs the transport; at either pole the latitude fibre collapses
to a point, giving continuity there for both map and inverse. The
one-dimensional starting case is the increasing cumulative map on a
circle with a fixed cut. The construction gives the measure identity
$F_{v,t}(h(\omega))^s\,d(h(\omega))=R_0^s\,d\omega$.
Now set

$$
 \mathcal T_v^\varepsilon(\lambda\omega)
   =\lambda\frac{F_{v,t}(h(\omega))}{R_0}h(\omega),
 \qquad 0\le\lambda<R_0.
 \tag{72.9}
$$

This is a homeomorphism, including at zero. Radial integration and the
spherical measure identity show that it preserves Lebesgue measure on
every measurable set, not only total volume. Equivalently its polar
Jacobian is one wherever differentiated. This verifies(72.6). These
transport maps are not used to assert uniform higher derivative bounds.
$\square$

**Theorem 72.6 (uniform local analytic constants for these varying chambers).**
For the chambers in72.5 and $s\ge3$, let $A_{0,v}^\varepsilon$ be the
mixed Laplacian, Dirichlet on the union $\Gamma_v^\varepsilon$ of its
plates and Neumann on the remaining chamber boundary. Let
$\Lambda_v^\varepsilon$ be the negative Dirichlet-to-Neumann operator
on these plates: its quadratic form is minus the harmonic extension's
Dirichlet energy. Its kernel consists of the single constant trace.
Let $\Pi_v^\varepsilon:L^2(\Gamma_v^\varepsilon)\to L^2(Q_v^\varepsilon)$
be the bounded extension of the zero-energy mixed harmonic lift. There
are constants $C_A,C_\Pi,C_0>0$, independent of $\varepsilon$, such that

$$
 \|(A_{0,v}^\varepsilon)^{-1}\|\le C_A\varepsilon,
 \qquad |\lambda_2(\Lambda_v^\varepsilon)|
       \ge\frac1{C_0\varepsilon},
 \qquad \|\Pi_v^\varepsilon\|\le C_\Pi.
 \tag{72.10}
$$

The constants can be chosen simultaneously over this fixed finite
double. They depend on $s$, its fixed reference volumes, degrees,
angular margins and transition profiles. In particular there is no
claim that they are uniform in $D$, $\delta$ or $s$.

**Proof.** The radial functions of $K_v(t)$ have bounds
$0<l\le F_{v,t}\le M$ and
$\|\nabla_{\mathbb S^{s-1}}F_{v,t}\|_\infty\le M_1$ independent of
$t$; truncation replaces a small cone cap by a plane with bounded radial
slope, and(72.4) adds a fixed smooth function with coefficient $O(t^s)$.
The elementary radial map from a ball to $K_v(t)$ and its inverse are
therefore uniformly Lipschitz, with constants controlled by
$l,M,M_1,s$. The ordinary Poincaré and Sobolev trace inequalities on a
ball, transferred by these maps, give constants $C_P,C_T$ such that

$$
 \|u-\bar u\|_{L^2(K_v(t))}\le C_P\|\nabla u\|_{L^2(K_v(t))},
 \qquad
 \|\operatorname{Tr}u\|_{L^p(\partial K_v(t))}
       \le C_T(\|u\|_2+\|\nabla u\|_2),
 \quad p=\frac{2(s-1)}{s-2}.
 \tag{72.11}
$$

Here $\bar u$ is the volume mean. To make the constants explicit in
fixed local data, let $P_s,T_s$ be Poincaré and $H^1$-to-$L^p$ trace
constants on the unit ball, set $L_+=M+M_1$ and
$B_\partial=M^{s-2}\sqrt{M^2+M_1^2}$, and take

$$
 C_P=(M/l)^{s/2}P_sL_+,\qquad
 C_T=B_\partial^{1/p}T_s l^{-s/2}\max\{1,L_+\}.
 \tag{72.11a}
$$

Indeed the radial map $x\mapsto F_{v,t}(x/|x|)x$ has derivative
norm at most $L_+$, volume Jacobian between $l^s$ and $M^s$,
and surface Jacobian at most $B_\partial$. For Poincaré, pull back to
the unit ball, subtract its volume mean, and then minimize over the
constant in the physical body. For the trace inequality use the same
change of variables and surface Jacobian. These are the standard
ball trace/Poincaré results, with their exact use and dependence given
by(72.11a); no derivative of the volume transport(72.9) is involved.
If $k$ is the degree, the plates in $K_v(t)$ have total measure
$k t^{s-1}$. Hölder's inequality in(72.11) yields

$$
 \|\operatorname{Tr}(u-\bar u)\|_{L^2(\Gamma_t)}^2
      \le C_0 t\|\nabla u\|_2^2,
 \qquad C_0=k^{1/(s-1)}C_T^2(1+C_P)^2.
 \tag{72.12}
$$

For zero plate trace this implies
$|\bar u|^2\le(C_0/k)t^{-(s-2)}\|\nabla u\|_2^2$.
Using the orthogonal volume-mean decomposition, for $0<t\le1$,

$$
 \|u\|_2^2\le C_A t^{-(s-2)}\|\nabla u\|_2^2,
 \qquad C_A=C_P^2+m_vC_0/k.
 \tag{72.13}
$$

This proves the mixed inverse bound on $K_v(t)$. If instead the plate
trace has integral zero, subtracting its volume mean can only increase
its squared plate norm. Thus(72.12) gives
$\|\operatorname{Tr}u\|_{L^2(\Gamma_t)}^2\le C_0t\|\nabla u\|_2^2$.
The variational characterization of the first nonconstant Steklov mode,
applied to its harmonic extension, gives its magnitude at least
$1/(C_0t)$. Connectedness gives the one-dimensional constant kernel.

Here is a local proof of the harmonic-lift bound that does not import
an unproved global mixed $H^2$ estimate. For each conical tip let $A_i$
be its untruncated apex. Choose a fixed collar wholly within its exact
conical neighbourhood and a smooth cutoff equal to one near the
truncated plate. In that collar set
$X_i(x)=\chi_i(x)(A_i-x)$, and set it zero outside. Collars are disjoint.
The sum $X$ satisfies, with a constant $C_X$ independent of $t$,

$$
 X\cdot\nu=qt\text{ on every plate},\qquad
 X\cdot\nu=0\text{ on the remaining boundary},\qquad
 \|X\|_\infty+\|DX\|_\infty\le C_X.
 \tag{72.14}
$$

The second identity holds because $A_i-x$ is tangent to the cone wall
and the cutoff vanishes before the wall ceases to be conical.
For $w=A_0(K_v(t))^{-1}f$, the classical Rellich multiplier identity,
with Dirichlet trace on the plates and Neumann trace elsewhere, gives

$$
 qt\|\partial_\nu w\|_{L^2(\Gamma_t)}^2
   \le C_R\bigl(\|\nabla w\|_2^2
                     +\|f\|_2\|\nabla w\|_2\bigr),
 \tag{72.15}
$$

where one may take $C_R=(s+4)C_X$. Indeed, integrate the divergence
of $X|\nabla w|^2-2\operatorname{Re}((X\cdot\nabla\bar w)\nabla w)$.
On a Dirichlet plate its boundary integrand is
$-(X\cdot\nu)|\partial_\nu w|^2$; on the Neumann part it is zero.
The interior terms are bounded by the right side of(72.15), since
$-\Delta w=f$.

The identity is valid for this mixed problem without global $H^2$.
For each fixed $t>0$ there are only smooth Dirichlet and Neumann faces
and smooth codimension-two rims. In a transverse wedge of angle
$\omega=\pi-\alpha$ the separated mixed angular modes have exponents
$(j+1/2)\pi/\omega$, $j\ge0$; the least is
$\lambda=\pi/(2\omega)>1/2$. The standard local mixed-edge
regularity argument (straighten the smooth rim, localize, and use these
angular modes with tangential Fourier localization) gives local
$H^{1+\lambda-\eta}$ regularity for every
$0<\eta<\lambda-1/2$, with the usual $H^2$ cap for the regular part.
In particular the face normal derivatives are in $L^2$.
For the primary three-dimensional mixed-edge spectrum and the
localization framework, see Monique Dauge,
[*Neumann and mixed problems on curvilinear polyhedra*](https://dauge.pages.math.cnrs.fr/publis/DaugeMixed92.pdf),
Section3, especially Notation3.3, and the dihedral analysis in
Sections8–10. The present rims have no conical vertices. In the local
model for dimension $s$, replace the single tangential Fourier variable
by $\xi\in\mathbb R^{s-2}$. The transverse equation contains the
same angular operator and the additional nonnegative term $|\xi|^2$;
its Mellin exponents at the rim are unchanged. The local weighted
energy estimates therefore integrate over these tangential variables
by Plancherel with the same admissible exponent interval. Flattening a
smooth rim freezes this transverse principal part; on a sufficiently
small chart its coefficient perturbation is absorbed in the strict
exponent margin, and the lower order terms are controlled by the
$H^1$ norm. For each fixed $t$ all chart coefficients are smooth and
bounded. This gives the asserted local regularity in every fixed $s$;
no uniform chart size as $t\downarrow0$ is needed.

Removing tubes of radius $b$ about the rims in the multiplier identity
and taking a sequence $b\downarrow0$ eliminates their boundary terms:
the worst mixed singular contribution is of order $b^{2\lambda-1}$,
with an arbitrarily small exponent loss if necessary, which tends to
zero. Approximation gives the identity for $L^2$ right-hand sides.
The regularity constants in this justification need only be finite for
each fixed $t$; the uniform constant in(72.15) comes solely from(72.14).
No uniform global $H^2$ estimate is asserted.

By(72.13) and the energy identity,
$\|\nabla w\|_2^2\le C_A t^{-(s-2)}\|f\|_2^2$.
Consequently(72.15) implies

$$
 \|\partial_\nu A_0(K_v(t))^{-1}f\|_{L^2(\Gamma_t)}
   \le C_\Pi t^{-(s-1)/2}\|f\|_2,
 \qquad
 C_\Pi^2=\frac{C_R}{q}(C_A+\sqrt{C_A}).
 \tag{72.16}
$$

Green's identity identifies the adjoint of the harmonic lift with
$-\partial_\nu A_0^{-1}$ on the plates. First use smooth traces, then
density and(72.16); this defines the required bounded lift on all plate
$L^2$ inputs and bounds its norm by $C_\Pi t^{-(s-1)/2}$.

Under the physical dilation by $r$, the mixed inverse norm gains
$r^2$, a Steklov eigenvalue gains $r^{-1}$, and the boundary-to-volume
lift norm gains $r^{1/2}$. The three scale identities are

$$
 r^2t^{-(s-2)}=\varepsilon,\qquad
 (rt)^{-1}=\varepsilon^{-1},\qquad
 r^{1/2}t^{-(s-1)/2}=1.
 \tag{72.17}
$$

They prove(72.10). The transverse Neumann gap of the fixed unit-area
disk cross-section, dilated by $\varepsilon$, is also a fixed positive
constant times $\varepsilon^{-2}$. For an edge's mixed problem
(Dirichlet on both plates, Neumann on its side), separation in these
transverse modes gives inverse norm at most $\pi^{-2}$. Its harmonic
lift has, for transverse wave number $b>0$, the two scalar factors
$\sinh(b(1-x))/\sinh b$ and $\sinh(bx)/\sinh b$; for $b=0$ these
are $1-x$ and $x$. Each factor is between zero and one. Squaring,
integrating and summing the orthonormal transverse modes therefore
gives an edge lift norm at most $\sqrt2$, uniformly in $\varepsilon$.
This supplies the full edge Poisson bound as well as the chamber bound.
Rigid motions affect none of these estimates. Taking maxima of
$C_A,C_\Pi,C_0$ over the finite vertex set makes them simultaneous.
$\square$

**Definition 72.7 (the full doubled effective space and the full-space lift).**
Let $\widehat G$ be the double from72.5. Its edges are oriented so that
reflection preserves the edge parameter $x\in(0,1)$. Put

$$
\begin{aligned}
 \widehat{\mathcal H}
  &=\bigoplus_{e\in\widehat E}L^2(0,1)\oplus\mathbb C^{\widehat V},
 &\kappa_v&=\sqrt{m_v},\\
 \operatorname{Dom}B
  &=\{(u,\beta):u_e\in H^2(0,1),\ u_e(v)=u_v
                \text{ for all incident }e,\ \beta_v=\kappa_vu_v\},\\
 B(u,\beta)&=\left((-u''_e)_e,
             \left(-\kappa_v^{-1}\sum_{e\sim v}
                         \partial_{\rm in}u_e(v)\right)_v\right).
\end{aligned}
\tag{72.18}
$$

This is the operator of equations(16)–(18) of the cited paper.
Equivalently its closed form is $\sum_e\int|u'_e|^2$, on the same
trace-matching domain with $H^1$ in place of $H^2$. Its Hilbert norm
is $\sum_e\|u_e\|_2^2+\sum_v|\beta_v|^2$; the $\beta_v$ are
independent coordinates before imposing a domain condition.

On the entire Hilbert space define
$\Theta_\varepsilon:\widehat{\mathcal H}\to L^2(\Omega_\varepsilon)$
by the following formulas in the rigid cylinder coordinates and chambers:

$$
 (\Theta_\varepsilon(u,\beta))|_{Q_e^\varepsilon}
     =\varepsilon^{-(s-1)/2}u_e(x),\qquad
 (\Theta_\varepsilon(u,\beta))|_{Q_v^\varepsilon}
     =\varepsilon^{-(s-1)/2}\frac{\beta_v}{\sqrt{m_v}}.
 \tag{72.19}
$$

Thus arbitrary cable $L^2$ inputs and arbitrary independent atomic
$\beta$ coordinates are included. The map is an isometry into physical
$L^2$, with closed proper range, not onto physical $L^2$. Its adjoint is

$$
\begin{aligned}
 (\Theta_\varepsilon^*h)_e(x)
  &=\varepsilon^{-(s-1)/2}
                       \int_{Q_e^{\rm c,\varepsilon}}h(x,y)\,dy,\\
 (\Theta_\varepsilon^*h)_v
  &=\varepsilon^{-(s-1)/2}m_v^{-1/2}
                       \int_{Q_v^\varepsilon}h(x)\,dx.
\end{aligned}
\tag{72.20}
$$

**Proof of the asserted normalization.** The edge factor is the normalized
constant transverse function, since each cross-section has measure
$\varepsilon^{s-1}$. The chamber contribution to its squared norm is
$\varepsilon^{-(s-1)}m_v^{-1}|\beta_v|^2|Q_v^\varepsilon|
=|\beta_v|^2$. The disjoint pieces therefore give
$\Theta_\varepsilon^*\Theta_\varepsilon=I$, and integration gives
(72.20). Nonconstant transverse functions and nonconstant chamber
functions exhibit the proper orthogonal complement. On the dense
operator domain, $\beta_v/\sqrt{m_v}=u_v$, so(72.19) agrees with the
paper's stated constant-mode lift. Its bounded extension supplies the
full Hilbert-space meaning of that lift; the word “onto” in the paper's
description cannot mean surjectivity onto all of $L^2(\Omega_\varepsilon)$.
$\square$

**Proposition 72.8 (the doubled correspondence is unitary onto the odd sector).**
Reflection exchanges $p_+$ with $p_-$ and $e_+$ with $e_-$, and fixes
each ground vertex $g$. Let $\widehat{\mathcal H}_{\rm odd}$ be its
negative eigenspace. Define a new map
$W_{\rm dbl}:\mathcal H_\delta\to\widehat{\mathcal H}_{\rm odd}$ by

$$
\begin{aligned}
 (W_{\rm dbl}F)_{e_+}&=\sqrt{\delta/2}\,u_e,
 &(W_{\rm dbl}F)_{e_-}&=-\sqrt{\delta/2}\,u_e,\\
 (W_{\rm dbl}F)_{p_+}&=f_p/\sqrt2,
 &(W_{\rm dbl}F)_{p_-}&=-f_p/\sqrt2,
 &(W_{\rm dbl}F)_g&=0.
\end{aligned}
\tag{72.21}
$$

The first row specifies edge coordinates; the second specifies atomic
$\beta$ coordinates. Its adjoint on the full doubled space is

$$
 (W_{\rm dbl}^*(u,\beta))_e
       =\frac{u_{e_+}-u_{e_-}}{\sqrt{2\delta}},\qquad
 (W_{\rm dbl}^*(u,\beta))_p
       =\frac{\beta_{p_+}-\beta_{p_-}}{\sqrt2}.
 \tag{72.22}
$$

The map $W_{\rm dbl}$ maps the entire target operator domain onto
$\operatorname{Dom}B\cap\widehat{\mathcal H}_{\rm odd}$, and

$$
 W_{\rm dbl}L=\frac a\delta BW_{\rm dbl},\qquad
 W_{\rm dbl}^*W_{\rm dbl}=I,\qquad
 W_{\rm dbl}W_{\rm dbl}^*=\widehat P_{\rm odd}.
 \tag{72.23}
$$

This $W_{\rm dbl}$ is different from the harmonic $W_N=E_NS_N$ of
Theorem64.6. Its domain is all atoms and all cable functions, not a
finite discrete occupation space; it performs doubling and normalization,
not harmonic calibration.

**Proof.** The two edge copies in(72.21) have total squared norm
$\delta\|u_e\|_2^2$ and the atomic copies have total squared norm
$|f_p|^2$. Conversely any odd vector has opposite source and edge
coordinates and zero fixed-ground coordinates, so(72.22) recovers it.
The adjoint uses the cable density $\delta$ in(72.2).

At a source endpoint $\kappa_p=1/\sqrt\delta$, hence
$\kappa_p\sqrt{\delta/2}u_e(p)=f_p/\sqrt2$ exactly when
$u_e(p)=f_p$. At a ground vertex oddness forces $\beta_g=0$.
The domain relation $\beta_g=\sqrt{m_g}u_g$ forces the grounded
trace $u_g=0$ because $m_g>0$. The two incident edge-inward derivatives
there are opposite, so the ground output of $B$ is also zero. This is
a consequence of the odd double, not a new flux condition at an original
port. The remaining domain conditions are exactly those of(72.3).
Substitution in(72.18) gives the cable coefficient $a/\delta$ and
atomic output $-a\sum\partial_{\rm in}u_e$ after(72.21).
Alternatively the doubled energy is $\delta\sum_e\int|u'_e|^2$;
multiplication by $a/\delta$ gives(72.2). Both arguments prove(72.23).
$\square$

**Proposition 72.9 (grounding by a normalized odd restriction).**
Let $A_\varepsilon$ be the all-Neumann Laplacian on the full
$\Omega_\varepsilon$, defined by its $H^1$ Dirichlet-energy form.
Set $\Omega_\varepsilon^+=\Omega_\varepsilon\cap\{x_3>0\}$ and
$\Sigma_\varepsilon=\Omega_\varepsilon\cap\{x_3=0\}$.
Let $A_\varepsilon^+$ be the operator represented by

$$
 q_\varepsilon^+[h]=\int_{\Omega_\varepsilon^+}|\nabla h|^2,
 \qquad
 \operatorname{Dom}q_\varepsilon^+
  =\{h\in H^1(\Omega_\varepsilon^+):
                         \operatorname{Tr}_{\Sigma_\varepsilon}h=0\}.
 \tag{72.24}
$$

This gives Dirichlet boundary on the cut and natural Neumann boundary
on the exterior. Define $S_\varepsilon$ from half-domain $L^2$ onto
the full odd space by

$$
 (S_\varepsilon h)(x)=
 \begin{cases}h(x)/\sqrt2,&x_3>0,\\
       -h(\mathcal R x)/\sqrt2,&x_3<0.
 \end{cases}
 \qquad
 (S_\varepsilon^*h)(x)
       =\frac{h(x)-h(\mathcal R x)}{\sqrt2},\quad x_3>0.
 \tag{72.25}
$$

Then $S_\varepsilon^*S_\varepsilon=I$,
$S_\varepsilon S_\varepsilon^*=P_{\rm odd}$, and
$S_\varepsilon A_\varepsilon^+
 =A_\varepsilon S_\varepsilon$ on their corresponding operator
domains. Also $\Theta_\varepsilon$ is reflection-equivariant.

**Proof.** Lipschitz trace and gluing across the cut show that a zero-trace
$H^1$ function extends oddly to $H^1$ on the full domain. Conversely
an odd $H^1$ function has zero cut trace and restricts to that form
domain. The normalized extension preserves both $L^2$ norm and
Dirichlet energy. Unitary equivalence of the represented forms gives
the stated operator-domain and resolvent identities. This uses no mixed
$H^2$ assertion at the cut/exterior intersection. Formula(72.19), the
reflected pieces and the even ground chambers prove equivariance.
$\square$

**Theorem 72.10 (correctly typed full physical norm-resolvent relation).**
For every fixed nonempty compact $K\subset\mathbb C\setminus\mathbb R$,
there are $\varepsilon_0>0$ and $C<\infty$ such that for
$0<\varepsilon<\varepsilon_0$,

$$
\begin{aligned}
 H_\varepsilon&=\frac a\delta A_\varepsilon^+,
 &J_\varepsilon&=S_\varepsilon^*\Theta_\varepsilon W_{\rm dbl}
       :\mathcal H_\delta\longrightarrow L^2(\Omega_\varepsilon^+),\\
 J_\varepsilon^*J_\varepsilon&=I,
 &\sup_{z\in K}\big\|(H_\varepsilon-z)^{-1}
       -J_\varepsilon(L-z)^{-1}J_\varepsilon^*\big\|
          _{\mathcal B(L^2(\Omega_\varepsilon^+))}
       &\le\frac\delta a C\varepsilon.
\end{aligned}
\tag{72.26}
$$

The physical generator scale is $a/\delta$. The estimate is on the
entire physical $L^2$ space, including its complement to
$\operatorname{Ran}J_\varepsilon$. It is not a root, harmonic,
edge-only or calibrated-state compression. Its constants can depend
on $D,\delta,a,s,(m_g)_g$, the chosen fixed geometry and $K$.
It supplies no uniformity for growing sources, shrinking $\delta$,
growing spectral sets or increasing $s$.

**Proof.** Verify first the precise interface to the mature convergence
theorem. The full structure is finite, connected and has straight
length-one cylinders with the fixed smooth unit-area cross-section
dilated by $\varepsilon$. Chambers are connected, have the smooth
noncontact boundary and flat contacts at angles uniformly below $\pi$
required in Section2. Their reference-volume representation is exactly
(72.6), with $|Q_v^0|=m_v>0$. The three local inputs of Section3,
Proposition3.1 and Lemmata3.3/3.5, are the explicit uniform bounds
(72.10); thus they are not inferred merely from a volume-preserving
homeomorphism. The transverse decoupling uses the fixed disk gap noted
in72.6. The longitudinal Dirichlet edge gap is $\pi^2$, and(72.10)
gives a uniform positive lower bound on the complete decoupled
operator for all sufficiently small $\varepsilon$. For the normalized
constant plate vector
$\psi_v=|\Gamma_v^\varepsilon|^{-1/2}\mathbf1$, harmonic extension is
the same constant throughout its chamber, so
$\|\Pi_v^\varepsilon\psi_v\|_2^2=m_v/k_v>0$ exactly. Thus the
finite-dimensional constant-mode lower bound used in the paper's
Section4 is uniform as well. Standard mixed transmission operators
are well defined on
these piecewise smooth Lipschitz pieces, with the local mixed normal
traces justified in72.6. The full exterior operator is all-Neumann,
exactly the operator considered by the paper. No mixed-exterior
convergence theorem is substituted for it.

Apply Theorem4.5, with equations(16)–(18) giving(72.18), on
$K'=(\delta/a)K$. This is a fixed compact nonreal set with

$$
 \sigma'=\frac\delta a\min_{z\in K}|\operatorname{Im}z|>0,
 \qquad R'=\frac\delta a\max_{z\in K}|z|<\infty.
 \tag{72.27}
$$

It lies in the paper's fixed $K_{\sigma'}$ class from Section2.
Only that fixed-set statement of Theorem4.5 is used, not a statement
uniform over growing-frequency sets or its additional analytic
continuation to real spectral gaps. Since $s\ge3$, its exponent
$\gamma$ is zero. In the full physical Hilbert space it gives

$$
 \sup_{\zeta\in K'}
 \|(A_\varepsilon-\zeta)^{-1}
       -\Theta_\varepsilon(B-\zeta)^{-1}\Theta_\varepsilon^*\|
       \le C\varepsilon.
 \tag{72.28}
$$

This is the paper's full resolvent theorem, rather than its
edge-compressed Theorem4.2. All normalizations in its constant-mode
map have the full-space extension(72.19).

Both terms in(72.28) reduce the odd subspace. Compress with
$S_\varepsilon^*$ and $S_\varepsilon$, each of norm one. On the
odd effective space use the onto unitary $W_{\rm dbl}$ and(72.23),
and set $\zeta=\delta z/a$. The scaling identities are

$$
 (H_\varepsilon-z)^{-1}
   =\frac\delta a S_\varepsilon^*
                      (A_\varepsilon-\zeta)^{-1}S_\varepsilon,
 \qquad
 W_{\rm dbl}(L-z)^{-1}W_{\rm dbl}^*
   =\frac\delta a(B-\zeta)^{-1}\widehat P_{\rm odd}.
 \tag{72.29}
$$

Equivariance and(72.29) turn(72.28) into(72.26). No factor two is
lost in the compression. The isometry statement follows because
$\Theta_\varepsilon W_{\rm dbl}$ has odd range and all three
identifications preserve the corresponding norms.

More explicitly, $J_\varepsilon F$ equals
$\sqrt\delta\,\varepsilon^{-(s-1)/2}u_e(x)$ on each upper cylinder,
$\sqrt\delta\,\varepsilon^{-(s-1)/2}f_p$ on each source chamber,
and zero on every upper half of a ground chamber. Its adjoint, with
respect to the norm(72.2), is

$$
\begin{aligned}
 (J_\varepsilon^*h)_p
    &=\sqrt\delta\,\varepsilon^{-(s-1)/2}
                                 \int_{Q_{p_+}^\varepsilon}h,\\
 (J_\varepsilon^*h)_e(x)
    &=\delta^{-1/2}\varepsilon^{-(s-1)/2}
                         \int_{Q_{e_+}^{\rm c,\varepsilon}}h(x,y)\,dy.
\end{aligned}
\tag{72.30}
$$

This also checks the actual atomic mass one and cable density $\delta$.
The ground chamber coordinates introduced in the full all-Neumann
supplier vanish in its odd effective sector; no ground atom is added
to the original source. Finite-thickness ground half-chambers do retain
physical $L^2$ functions, and(72.26) controls their resolvent responses
as part of the full physical norm. In particular it implies
$\|(H_\varepsilon-z)^{-1}(I-J_\varepsilon J_\varepsilon^*)\|
\le(\delta/a)C\varepsilon$ uniformly on $K$, not their deletion
from the physical carrier. $\square$

**Proposition 72.11 (finite thickness does not give an exact operator
intertwiner).** The map $J_\varepsilon$ in72.10 is not an exact
finite-thickness operator intertwiner between $L$ and $H_\varepsilon$.

**Proof.** On graph form inputs, its piecewise constant chamber values
and its cylinder functions match across the plates. But for a graph
operator input with a nonzero endpoint cable derivative, its cylinder
normal derivative at that plate is nonzero while its chamber derivative
is zero. The weak physical Laplacian then has an interface distribution
and is not represented by an $L^2$ function. Such inputs belong to
(72.3): for example give one cable a smooth endpoint-zero function with
nonzero derivative at a source end, set all other cables and all atomic
values to zero, and use(72.3) for its nonzero atomic output. This input
has the required zero grounded trace as well. Thus its $J_\varepsilon$
image fails the physical operator-domain transmission condition.
It follows that an identity $H_\varepsilon J_\varepsilon
=J_\varepsilon L$ on all of $\operatorname{Dom}L$ is false.
The resolvent estimate(72.26) asserts convergence and is compatible
with this domain failure. $\square$

**Proposition 72.12 (the planar separated-window logarithmic obstruction).**
Suppose instead that $s=2$, that a connected planar chamber has scale
$r=\sqrt\varepsilon$, and that its contact boundary contains at least
two windows, each of length $\varepsilon$, whose mutual distances
are at least $c r$ for a fixed $c>0$. Suppose all other contact windows
are separated by the same margin. Define the negative mixed
Dirichlet-to-Neumann map on the union of windows by its harmonic
energy form, with Neumann boundary elsewhere. Whenever these form
traces are defined on a Lipschitz chamber, its first nonzero Steklov
magnitude obeys

$$
 |\lambda_2|\le\frac{C}{\varepsilon|\log\varepsilon|}
 \tag{72.31}
$$

for all small $\varepsilon$. Consequently there is no positive
$\varepsilon$-independent lower constant $c_1$ with
$|\lambda_2|\ge c_1/\varepsilon$ for this separated-window family.

**Proof.** Centre a disk at the midpoint of each of two chosen windows.
Take an inner radius $b=C_b\varepsilon$ containing the entire window
and an outer radius $R=c_b r$, with fixed $c_b>0$ small enough that
these outer disks are disjoint and meet no other contact window.
On the plane define

$$
 \eta_i(x)=
 \begin{cases}
 1,&|x-x_i|\le b,\\
 \displaystyle\frac{\log(R/|x-x_i|)}{\log(R/b)},
                              &b<|x-x_i|<R,\\
 0,&|x-x_i|\ge R.
 \end{cases}
 \tag{72.32}
$$

Its energy on the whole annulus is $2\pi/\log(R/b)$, so restriction
to the chamber has no larger energy. The trace of $u=\eta_1-\eta_2$
is $+1$ and $-1$ on the two selected windows and zero on all others.
It has zero integral on the contact union and squared contact norm
$2\varepsilon$. Since
$\log(R/b)=\tfrac12|\log\varepsilon|+O(1)$, the trial energy is at
most $C/|\log\varepsilon|$. Its mixed harmonic extension minimizes
energy among functions with that contact trace and hence has no larger
energy. The Steklov variational principle now gives(72.31). In the
case of two windows alone the same proof applies without the additional
separation clause. Comparable unequal window lengths can also be
handled by balancing the two constant trace coefficients.
Multiplication of(72.31) by $\varepsilon$ tends to zero, contradicting
any positive fixed lower constant $c_1$.

This is the classical logarithmic-capacity cutoff calculation applied
to the actual small-window scale. It identifies a limitation of an
automatic $c/\varepsilon$ local gap, including an unqualified use of
the paper's Lemma3.5 for separated planar contacts. It is neither a
nonexistence proof for planar thin domains nor a counterexample to the
paper's final $O(\varepsilon|\log\varepsilon|)$ convergence rate:
that rate allows logarithmic losses, and its validity in such a planar
family requires its own complete applicability argument. $\square$

**Assumption 72.13 (unchanged source and realization obligations).**
The planar prescribed-metric problem for an arbitrary authentic tree
remains unresolved here: all centre-to-centre lengths must equal
$1+h_v+h_w$, both distinct ground stubs at every leaf must end on one
line, and the embedding must retain crossing-free clearance and port
margins. In the plane a leaf's prescribed-distance circle has only two
intersections with the grounding line, so72.3's azimuth argument does
not apply. Topological planarity supplies no such metric construction.
By contrast72.3–72.10 work for every fixed integer $s\ge3$; they do
not select uniquely three dimensions or prove a physical dimension law.

The full source and correspondence assumptions of71.2 and
Definitions66.10,67.11,68.7 remain in force. In particular retain every
literal label, bracket, left/right order and distinct occurrence,
immutable INITIAL, the fixed cap, source-independent original actor
initialization, complete supplied contexts, whole candidates and their
original guards, every acceptance/refusal, original Read, absorbing
Stop and every actually acquired record. The original actor's arbitrary,
unbounded or possibly zero $a$, untagged radius-$7/25$ $b$, destructive
actions and joint history-dependent errors are distinct from the fixed
positive commissioned $a$ of72.1. No new source service, ingress or
operation is supplied by a Euclidean embedding.

The entire $N=2$ symmetric literal-hardcore space of64.5 remains:
distinct atomic pairs, both orders of atom/cable slices, different-cable
rectangles and both dissected same-cable triangles, with weights
$1,\delta,\delta^2$, all port/ground/collision matching conditions,
including shared-port collisions, and no arbitrary $H^1$ corner-value
assumption. Both complete common and killed pair laws remain separate,
as do the declared one-body field and actual graft changes of root and
degrees. The free $N=1$ theorem constructs none of these two-particle,
interaction, field-mediator or switching correspondences.

Every field mode and spectator, unknown particle/field/auxiliary
correlation, the complete norm, common reference and clock are retained.
Unknown-state ingress, recovery, original Read/Stop covariance, actual
native operation and domain/dynamic correspondence, preparation,
harmonic/projection control, retained complement and cross-block control
remain independent requirements. An alternative encoded or separate
carrier must supply and prove those recovery/read/operation and dynamic
relations; an abstract Hilbert-space isomorphism, a source copy, a static
Green fit or calibrated-state re-preparation does not suffice.
There is no hidden trace, reset, cloning, independent resampling,
separate optimum asserted jointly, or exact-limit Read in72.26.
The doubled supplier and odd restriction are mathematical identifications,
not an acquired native operation or a new retained source state.

The common $\Pi$ of63.13 retains its full-vector/spanning, common-zero,
whole quadratic-distance/positive-semidefinite Gram, at least two
independent directions, alternating bilinear exact-area/Jacobi, actual
orthonormal-probe, finite binary-calibration and hidden-kernel-preserving
generator assumptions. Section57's immutable composition-promised
endpoint acquisition retains its depth caps, common source-independent
initialization, actual query/reply histories, correct finite stopping on
every promised positive and negative source, and distinct actual-address
fees, with no old-source archive. The separate paid positive-root
archive/nonadvancing-cut acquisition retains its exact port, finite
stopping/decoding, protected records after refusal/closure, aligned actual
generation, trusted markers, no unrecorded source change, closed strong
ports and actual write/protect/retain/query rights; all reply-affecting
retained source influence belongs in its service price. The phase-coherent
full-tail acquisition retains its separate once-sampled-depth actual Read
process and paid stopped transcript. None of their radii, state counts,
update rules or clocks is transferred to this thin-domain theorem.

An actual spatial interpretation still requires the original
operation/metric bridge, isotropic local physical mediators for both
complete pair prescriptions, packing, transverse, exterior, leakage and
collision controls, reference preparation and actual clock calibration.
Every construction, acquisition, preparation, field/compensation/stiffness
installation, control, service, production, storage, hold, retention,
maintenance, precision and total lifetime price remains an obligation.
The volume ratios and the physical generator scaling are mathematical
normalizations, not free controls, measured apparatus prices or physical
validation. The entire sustained why-three/source/native/field/acquisition/
resource objective remains beyond this fixed-source free-kinetic result.

## 72.99 追加锚（本行以下为增补区）

## 73. The entire free symmetric two-particle limit and literal hard-core separation

**Definition 73.1 (fixed product data).** Fix exactly Definition72.1's source,
parameters, geometry and grounding. Write $\mathcal H=\mathcal H_\delta$,
$\mathcal Q=\mathcal Q_\delta$, and $L=A_{\delta,D,1}$ as in (72.2)–(72.3).
The free comparison space is
$\mathcal H_2^{\rm fr}=L^2_{\rm sym}(X_D^2,\mu_\delta^{\otimes2})$.
Ordered coordinates before exchange restriction give $n^2$ atomic pairs,
$4n^2$ atom/cable slices and $4n^2$ cable/cable cells. In particular each
$(p,p)$ has mass one; ground endpoints have no atomic coordinate.
Every same-cable square is retained. Its diagonal has
zero two-dimensional measure; this does not impose a zero collision trace.
For $F=(F_{pq},F_{pe},F_{ep},F_{ef})$, the norm is

$$
\|F\|^2=\sum_{p,q}|F_{pq}|^2
 +\delta\sum_{p,e}(\|F_{pe}\|_2^2+\|F_{ep}\|_2^2)
 +\delta^2\sum_{e,f}\|F_{ef}\|_2^2.                 \tag{73.1}
$$

There is no additional normalization on the symmetric subspace. Symmetry means
$F_{pq}=F_{qp}$, $F_{pe}(y)=F_{ep}(y)$ and
$F_{ef}(x,y)=F_{fe}(y,x)$.
Define $\mathcal Q_2^{\rm fr}$ by $H^1$ slices and $H^1$ full rectangles,
with these trace conditions: a cell boundary at a source port equals the
corresponding atom/cable slice in $L^2$; a slice endpoint at a source port
equals its atomic pair value; grounded ends give zero in either coordinate.
Explicitly, if $e$ meets $p$ and $f$ meets $q$,

$$
\operatorname{Tr}_xF_{ef}(p,y)=F_{pf}(y),\qquad
\operatorname{Tr}_yF_{ef}(x,q)=F_{eq}(x),\qquad
F_{eq}(p)=F_{pq}=F_{pf}(q).
$$

All incident boundaries use the same slice, including at shared ports.
Thus incident slices approaching $(p,p)$ end at $F_{pp}$, which is allowed
to be nonzero. On a dissected same-cable square the two diagonal traces
agree, with no requirement that they vanish. This is equivalent to $H^1$
on its full square. No point trace of an arbitrary rectangle at a corner
is used. Put

$$
q_2^{\rm fr}[F]=a\left[
 \sum_{e,q}\|\partial_xF_{eq}\|_2^2
 +\sum_{p,f}\|\partial_yF_{pf}\|_2^2
 +\delta\sum_{e,f}\int_{(0,1)^2}
       (|\partial_xF_{ef}|^2+|\partial_yF_{ef}|^2)\right].
                                                               \tag{73.2}
$$

**Theorem 73.2 (complete free product limit).** The form (73.2) on
$\mathcal Q_2^{\rm fr}$ is densely defined, closed and nonnegative. Its
operator is
$B=(L\otimes I+I\otimes L)|_{\rm sym}$ on the entire
$\mathcal H_2^{\rm fr}=\operatorname{Sym}(\mathcal H\otimes\mathcal H)$.
On $\mathcal P_{\varepsilon,2}=L^2_{\rm sym}((\Omega_\varepsilon^+)^2)$ let
$B_\varepsilon=(H_\varepsilon\otimes I+I\otimes H_\varepsilon)|_{\rm sym}$,
where $H_\varepsilon$ and $J_\varepsilon$ are precisely (72.26), and set
$J_{\varepsilon,2}=(J_\varepsilon\otimes J_\varepsilon)|_{\rm sym}$.
Exact coincidence exclusion by the mixed-ground symmetric smooth-core
$H^1$ closure gives this same physical operator. For every fixed compact
$K\subset\mathbb C\setminus\mathbb R$,

$$
J_{\varepsilon,2}^*J_{\varepsilon,2}=I,\qquad
\eta_\varepsilon(K):=\sup_{z\in K}
 \|(B_\varepsilon-z)^{-1}
   -J_{\varepsilon,2}(B-z)^{-1}J_{\varepsilon,2}^*\|
 \longrightarrow0.                                             \tag{73.3}
$$

The norm is on the full physical symmetric space. No rate is asserted.

**Proof: domain in both directions.** The finite interval $H^1$ embeddings
and finite atomic space make $\mathcal Q\hookrightarrow\mathcal H$ compact.
The nonnegative self-adjoint $L$ consequently has an orthonormal eigenbasis
$\psi_j$, with eigenvalues $\lambda_j\ge0$.
For $F=\sum c_{jk}\psi_j\otimes\psi_k$, the tensor sum has form domain
and operator domain respectively

$$
\sum_{j,k}(1+\lambda_j+\lambda_k)|c_{jk}|^2<\infty,
\qquad
\sum_{j,k}(1+(\lambda_j+\lambda_k)^2)|c_{jk}|^2<\infty. \tag{73.4}
$$

On the symmetric space $c_{jk}=c_{kj}$. Finite symmetric truncations are
a form core. The first condition is exactly membership in the two
Bochner spaces $L^2(X_D,\mu_\delta;\mathcal Q)$, taking sections in each
variable, with their integrated form norms.
Such sections give $H^1$ atom/cable slices and both weak derivatives in
$L^2$ on every cell. The section endpoint identities give exactly the
cell-boundary/slice and slice-endpoint/atom identities in Definition73.1.
For an $H^1$ rectangle, the boundary trace agrees almost everywhere with
the one-dimensional section endpoints: approximate by smooth functions
and use the continuous $H^1\to L^2$ boundary trace. This also handles
each grounded boundary.
Conversely, the stipulated cell $H^1$ regularity, boundary traces and slice
$H^1$ endpoints imply these same section identities almost everywhere;
Fubini then puts the sections in $\mathcal Q$ in each direction with
finite integrated form norms. There is no further corner condition.
Integrating the one-coordinate energy against the other coordinate's
atomic and cable measures gives exactly (73.2), with weights $1$ on
slice derivatives and $\delta$ on cell derivatives. This proves the
domain equality, both directions of the tensor identification, and the
represented operator assertion. Spectral truncation proves density and
closedness without assuming multidimensional $H^2$ regularity.

**Proof: physical domain and the two Hilbert-space maps.** The same
section argument for (72.24) identifies the physical tensor form with

$$
\frac a\delta\int_{(\Omega_\varepsilon^+)^2}
 (|\nabla_xU|^2+|\nabla_yU|^2),                         \tag{73.5}
$$

on symmetric $H^1$ functions with zero traces on
$\Sigma_\varepsilon\times\Omega_\varepsilon^+$ and
$\Omega_\varepsilon^+\times\Sigma_\varepsilon$; exterior Neumann walls
give no essential form condition.
Here the trace domain equals the mixed-ground smooth-core closure.
Indeed extend oddly across each flat cut as in72.9, extend from the
bounded Lipschitz doubled product to ambient $H^1$, and project the
extension to be odd in each cut coordinate. Cut it off for
$|x_3|<h$ and $|y_3|<h$. The one-dimensional Hardy bound
$\int |v(r)|^2/r^2\,dr\le4\int |v'(r)|^2\,dr$ for zero-trace sections
follows on each half-line by integration by parts and Cauchy–Schwarz:
$\int |v|^2/r^2=2\operatorname{Re}\int v'\overline v/r
\le2\|v'\|_2\|v/r\|_2$, followed by odd smooth approximation.
It makes each derivative-cutoff error tend to zero by absolute continuity
of the integral on the shrinking layer. Smooth approximation away from
the cuts and exchange averaging finish the core approximation.
The converse follows from continuity of the grounded trace.
The fixed-positive-thickness capacity input now applies: for $s\ge2$
the physical coincidence diagonal has zero $H^1$ capacity, and its
specified closure leaves this mixed-ground symmetric form unchanged.
Our fixed $s\ge3$ and positive constant $a/\delta$ meet those hypotheses.
The diagonal is also Lebesgue-null, so the physical Hilbert space is
unchanged. This reuses that capacity fact, not a thin-limit conclusion
or a classification of contact extensions.

For explicit forward and adjoint maps put
$c_\varepsilon=\sqrt\delta\,\varepsilon^{-(s-1)/2}$.
Let $Z_p=Q_{p_+}^\varepsilon$ be a source chamber and
$Z_e(x)=Q_{e_+}^{\rm c,\varepsilon}$ a cable cross-section at $x$.
On every ordered chamber/chamber, chamber/cylinder, cylinder/chamber
and cylinder/cylinder product, respectively, the lift is
$c_\varepsilon^2F_{pq}$, $c_\varepsilon^2F_{pe}(y)$,
$c_\varepsilon^2F_{ep}(x)$ and $c_\varepsilon^2F_{ef}(x,y)$.
It is zero when either coordinate lies in a ground half-chamber.
For $\alpha,\beta$ each a port or cable, its adjoint is

$$
(J_{\varepsilon,2}^*U)_{\alpha\beta}
 =b_\alpha b_\beta
     \int_{Z_\alpha\times Z_\beta}U,\qquad
b_p=c_\varepsilon,\quad b_e=c_\varepsilon/\delta.       \tag{73.6}
$$

Cable longitudinal variables remain unevaluated in this integral.
The volumes $|Z_p|=\varepsilon^{s-1}/\delta$ and
$|Z_e|=\varepsilon^{s-1}$ give exactly (73.1) and
$J_{\varepsilon,2}^*J_{\varepsilon,2}=I$.
These formulas act on all Hilbert data, including independent atomic
coordinates, and commute with exchange. They give a proper range:
nonconstant transverse/chamber modes and ground half-chamber functions
remain in the physical carrier.

**Proof: full resolvent convergence.** For $f\in C_0([0,\infty))$ put
$\Phi_\varepsilon(f)=J_\varepsilon f(L)J_\varepsilon^*$.
The isometry makes this a multiplicative, adjoint-preserving map, even
though it is not unital on physical $L^2$.
Theorem72.10 at $i$ and $-i$ implies
$\|f(H_\varepsilon)-\Phi_\varepsilon(f)\|\to0$ for every such $f$.
To see this, first take polynomials without constant term in
$(t-i)^{-1}$ and $(t+i)^{-1}$, telescope their products, and then use
uniform approximation. Their self-adjoint algebra separates points,
vanishes nowhere on $[0,\infty)$ and is dense in $C_0$ by
Stone–Weierstrass; both functional calculi are contractions.
For each $t>0$ this applies to $f_t(\lambda)=e^{-t\lambda}$.
Tensoring the two semigroups gives the full unsymmetrized estimate

$$
\|e^{-t(H_\varepsilon\otimes I+I\otimes H_\varepsilon)}
 -(J_\varepsilon\otimes J_\varepsilon)
 e^{-t(L\otimes I+I\otimes L)}
 (J_\varepsilon^*\otimes J_\varepsilon^*)\|
 \le2\|e^{-tH_\varepsilon}-\Phi_\varepsilon(f_t)\|\to0. \tag{73.7}
$$

All operators commute with exchange, so compression gives the same
conclusion on the full symmetric space. Integrating against $e^{-t}dt$
and using the contraction bound proves (73.3) first at $z=-1$.
There is no assertion of convergence at $t=0$; that single endpoint
does not affect dominated convergence of the integral.
For nonreal $z$ use
$h_z(r)=r/[1-(z+1)r]$ on $[0,1]$. It is continuous and $h_z(0)=0$.
Polynomial approximation on $[0,1]$ shows that applying it to the two
converging negative resolvents gives (73.3),
since its value on the proper-range complement is zero. Uniformity
on compact $K$ follows from a finite net and the resolvent identity,
whose Lipschitz bound is $|z-w|/(|\operatorname{Im}z|
|\operatorname{Im}w|)$ for either resolvent family.

Finally put $P_\varepsilon=J_{\varepsilon,2}J_{\varepsilon,2}^*$ and
$Q_\varepsilon=I-P_\varepsilon$. The comparison resolvent has only a
$P_\varepsilon$–$P_\varepsilon$ block. Consequently each of
$Q_\varepsilon(B_\varepsilon-z)^{-1}Q_\varepsilon$,
$P_\varepsilon(B_\varepsilon-z)^{-1}Q_\varepsilon$ and
$Q_\varepsilon(B_\varepsilon-z)^{-1}P_\varepsilon$ has norm at most
$\eta_\varepsilon(K)$, as does the difference of the two
$P_\varepsilon$–$P_\varepsilon$ blocks. This retains the entire
complement and both cross blocks. $\square$

**Theorem 73.3 (explicit separation from the unchanged comparator).**
Let $E:\mathcal K_{D,2}^{\rm hc}\to\mathcal H_2^{\rm fr}$ be the isometry
identifying all slice/cell $L^2$ coordinates and inserting zero at every
$(p,p)$. Its range is precisely $\{F:F_{pp}=0\text{ for all }p\}$.
Under $E$, Definition64.5's form domain is exactly

$$
\{F\in\mathcal Q_2^{\rm fr}:F_{pp}=0\ (p\in D),\quad
           \operatorname{Tr}_{x=y}F_{ee}=0\ (e\in\mathcal E_D)\}.
                                                               \tag{73.8}
$$

Indeed zero diagonal traces glue the two triangles into an $H^1$ square;
the converse is restriction to those triangles. Slice endpoints at the
missing atoms are zero, including shared-port collisions. Other rectangles,
both slice orders, all grounded traces and every kinetic coefficient remain
exactly (64.7). No rectangle-corner trace is introduced.
Keep the original operators $A_{\delta,D,2}$ and
$\mathcal T^\diamond_{\delta,D,2}=A_{\delta,D,2}+U^\diamond_{D,2}$,
separately for $\diamond\in\{\mathrm c,\mathrm k\}$, with precisely

$$
U^\diamond_{D,2}(x,y)=-g(\phi_A(x)+\phi_A(y))
 -\nu\mathbf1_{x=p,y=q\in D,\ p\ne q}G_D^\diamond(p,q). \tag{73.9}
$$

Here $\phi_A$ is zero on open cables. Both complete pair prescriptions,
all ten coefficients of Definition64.1, including
$G^{\rm c}(LL,LR)=3/16$, and every original parameter are unchanged.
For any port $p$, let $k=d_p$ be its actual incidence and define

$$
N_p=1+\frac{13}{35}\delta k,\qquad
c_p=\left(N_p^2+\frac{24a^2kN_p}{\delta}
                    +\frac{72a^2k^2}{25}\right)^{-1/2}>0. \tag{73.10}
$$

For each $C\in\{A_{\delta,D,2},\mathcal T^{\rm c}_{\delta,D,2},
\mathcal T^{\rm k}_{\delta,D,2}\}$, at the specified nonreal parameter $i$,

$$
\begin{aligned}
\|(B-i)^{-1}-E(C-i)^{-1}E^*\|&\ge c_p,\\
\liminf_{\varepsilon\downarrow0}
 \|(B_\varepsilon-i)^{-1}
  -J_{\varepsilon,2}E(C-i)^{-1}E^*J_{\varepsilon,2}^*\|&\ge c_p.
\end{aligned}                                                    \tag{73.11}
$$

**Proof.** Let $e_{pp}$ be the normalized mass-one atomic basis vector.
Then $E^*e_{pp}=0$ for every comparator above. Construct
$f\in\operatorname{Dom}L$ with atomic value one at $p$ and zero at other
ports. On each cable incident at $p$, in distance $x$ from $p$, take
$b(x)=1-3x^2+2x^3$; all other cables are zero. The authentic tree has no
loops. The conditions $b(0)=1$, $b(1)=0$ and $b'(0)=b'(1)=0$ meet every
port/ground condition and give zero atomic output of $Lf$. Direct integration
and (72.3) give

$$
\|f\|^2=N_p,\qquad
\langle Lf,f\rangle=\frac65ak,\qquad
\|Lf\|^2=\frac{12a^2k}{\delta}.                         \tag{73.12}
$$

The symmetric $v=f\otimes f$ belongs to $\operatorname{Dom}B$ and
$\langle e_{pp},v\rangle=1$. Self-adjointness gives

$$
\begin{aligned}
1&=|\langle(B-i)^{-1}e_{pp},(B+i)v\rangle|
 \le\|(B-i)^{-1}e_{pp}\|\,\|(B+i)v\|,\\
\|(B+i)v\|^2
 &=N_p^2+2\|Lf\|^2N_p+2|\langle Lf,f\rangle|^2=c_p^{-2}.
\end{aligned}                                                    \tag{73.13}
$$

Thus the first discrepancy, tested on $e_{pp}$, is at least $c_p$.
No hypothesis on the comparator's potential beyond its declared
self-adjointness is needed; its resolvent annihilates this input after
embedding. Isometric conjugation preserves operator norms, so the second
bound follows from (73.3) and the reverse triangle inequality.
The witness supplies the positive gap after the full-space convergence
proof; it does not substitute a test subclass for that theorem. $\square$

**Scope and references.** The one-particle premise is precisely72.10,
with its fixed-source applicability checks for Cherednichenko–Ershova–Kiselev,
arXiv:2205.04397v4, Theorem4.5. The fixed-thickness capacity premise is the
mixed-ground symmetric smooth-core conclusion supported by Evans–Gariepy,
*Measure Theory and Fine Properties of Functions* (1992), §4.7.2, Theorem3,
pp.154–156; it is used only within its stated scope. The product inference
and constant (73.10) are proved above. No N1 rate is transferred, no
finite-radius/contact model is analyzed, and no source-growth uniformity
or uniquely three-dimensional conclusion follows.

The free comparison includes atomic double occupation and all continuum
strata; it leaves Definition64.5 as the literal hard-core target.
Equation (73.11) obstructs the compatible free-kinetic/exact-coincidence
route to that target, including its declared bounded operators. It
constructs no physical potential, field mediator or switching mechanism.
Every obligation of72.13,66.10,67.11 and68.7 remains: the complete literal
source, INITIAL/cap, original actor parameters and initialization, whole
contexts/candidates/guards, native acceptance/refusal/Read/absorbing Stop
and acquired records; every field mode, spectator and unknown correlation,
full norm, common reference and clock; ingress/recovery and actual
operation/domain/dynamic correspondence; all distinct acquisition promises,
fees, protected records and actual service rights; packing, leakage,
preparation, control, precision and total lifetime resources. A different
interaction, occupation penalty, identification or native carrier would
require its own proofs of all these bridges. This ordinary fixed-source
composition supplies neither physical validation nor completion of the
sustained programme.

## 73.99 追加锚（本行以下为增补区）
