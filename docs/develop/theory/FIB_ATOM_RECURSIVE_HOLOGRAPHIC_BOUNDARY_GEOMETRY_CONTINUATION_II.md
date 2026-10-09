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

## 74. Scattering strength and support range obstruct the literal hard-core limit

**Definition 74.1 (fixed data, unchanged target and full comparisons).** Fix
an arbitrary authentic finite nonempty $D$, commissioned $a>0$, one
$0<\delta\le1$, one integer $s\ge3$, and precisely the physical geometry,
grounding and fixed reference volumes of Definition72.1. All these data are
fixed as $\varepsilon\downarrow0$. Put $\beta=a/\delta$ and fix $M\ge0$.
Write $\Omega=\Omega_\varepsilon^+$,
$\mathcal P_\varepsilon=L^2_{\rm sym}(\Omega^2)$, and
$\mathcal Q_{\rm mix,\varepsilon}$ for the symmetric $H^1(\Omega^2)$
domain with the two grounded zero traces specified in (73.5). Its kinetic
form is

$$
q_{0,\varepsilon}[U]=\beta\int_{\Omega^2}
 (|\nabla_xU|^2+|\nabla_yU|^2).
\tag{74.1}
$$

Use exactly $E$ of Theorem73.3 and $J_{\varepsilon,2}$ of
(73.3)/(73.6). For each of the three original operators separately put

$$
\begin{aligned}
 C&\in\{A_{\delta,D,2},\mathcal T^{\rm c}_{\delta,D,2},
                         \mathcal T^{\rm k}_{\delta,D,2}\},\\
 K_{\varepsilon,C}
   &=J_{\varepsilon,2}E(C-i)^{-1}E^*J_{\varepsilon,2}^*.
\end{aligned}
\tag{74.2}
$$

Thus the target is the actual $\mathcal K_{D,2}^{\rm hc}$ of
Definition64.5: all distinct atomic pairs, both orders of mixed slices,
all different-cable rectangles and both triangles of every same-cable
square, with norm weights $1,\delta,\delta^2$, unchanged kinetic
coefficients, all port and ground matching, zero same-cable collision
traces and the shared-port zero atomic collision endpoint conditions.
There is no rectangle-corner point-trace assumption. Both pair laws
retain their entire original source functions and the same one-body field:

$$
 U^\diamond_{D,2}(x,y)=-g(\phi_A(x)+\phi_A(y))
 -\nu\mathbf1_{x=p,y=q\in D,\ p\ne q}G_D^\diamond(p,q),
 \qquad \diamond\in\{\mathrm c,\mathrm k\}.
\tag{74.3}
$$

Here $\phi(p)=2^{-|p|}$ and $\phi_A$ is zero on open cables; the pair
term is zero off distinct atomic pairs. In particular, on the original
five-port witness $(o,L,R,LL,LR)$ all ten entries remain

$$
\begin{array}{c|cccccccccc}
\{p,q\}&oL&oR&oLL&oLR&LR&L\,LL&L\,LR&R\,LL&R\,LR&LL\,LR\\ \hline
G^{\rm c}&1/2&1/2&1/4&1/4&1/4&3/8&3/8&1/8&1/8&3/16\\
G_D^{\rm k}&9/26&7/26&3/26&3/26&3/26&5/26&5/26&1/26&1/26&5/78
\end{array}
$$

This table records Definition64.1's witness; for general $D$ the complete
original laws, rather than a selected table or a fitted coefficient,
are the comparators. The physical multipliers introduced next are
additional model hypotheses and do not supply (74.3) or a native force.

**Definition 74.2 (the two interaction models and Dirichlet exclusion).**
In the soft scattering model let $h_\varepsilon\ge0$ satisfy
$h_\varepsilon=o(\varepsilon)$. Let
$v_\varepsilon:\mathbb R^s\to[0,\infty)$ be radial, measurable,
supported in $\{|r|\le h_\varepsilon\}$ and bounded for each individual
$\varepsilon$; its bound may grow without restriction. Let
$W_\varepsilon(x,y)$ be real, exchange symmetric and
$\|W_\varepsilon\|_\infty\le M$. The physical operator
$\mathsf H_\varepsilon$ is represented by exactly

$$
q_\varepsilon[U]=q_{0,\varepsilon}[U]
 +\int_{\Omega^2}(v_\varepsilon(x-y)+W_\varepsilon(x,y))|U|^2,
 \qquad U\in\mathcal Q_{\rm mix,\varepsilon}.
\tag{74.4}
$$

There is no additional form restriction. For the separate support-range
model take any $R_\varepsilon\to0$ and any nonnegative measurable
exchange-symmetric $V_\varepsilon(x,y)$ supported in
$|x-y|\le R_\varepsilon$. Its form is (74.4) with $v_\varepsilon(x-y)$
replaced by $V_\varepsilon$, on the natural sum domain

$$
\mathcal Q_{V,\varepsilon}
 =\left\{U\in\mathcal Q_{\rm mix,\varepsilon}:
                    \int V_\varepsilon|U|^2<\infty\right\}.
\tag{74.5}
$$

The stipulated model requires this natural sum form to be densely
defined on $\mathcal P_\varepsilon$. Its closedness follows by taking
limits in both the mixed $H^1$ form norm and the closed multiplication
norm $\|\sqrt{V_\varepsilon}U\|_2$. No other form restriction is
permitted. In particular there is no radiality, height bound or
$R_\varepsilon=o(\varepsilon)$ hypothesis in this model. Dense definition
is a stated domain requirement, not an inference from measurability
alone. Bounded $W_\varepsilon$ leaves both form domains unchanged.
Both represented operators are self-adjoint and bounded below by $-M$.
For either soft model define the discrepancy

$$
\Delta_{\varepsilon,C}
 =\| (\mathsf H_\varepsilon-i)^{-1}-K_{\varepsilon,C}\|
                      _{\mathcal B(\mathcal P_\varepsilon)}.
\tag{74.6}
$$

An ideal hard ball of radius $r>0$ has a different Hilbert carrier. Put

$$
\begin{aligned}
 G_{\varepsilon,r}&=\{(x,y)\in\Omega^2:|x-y|>r\},
 &\mathcal P_{\varepsilon,r}&=L^2_{\rm sym}(G_{\varepsilon,r}),\\
 \iota_r&:\mathcal P_{\varepsilon,r}\longrightarrow\mathcal P_\varepsilon,
 &\iota_r U&=\text{zero extension},\\
 \mathcal Q_{\varepsilon,r}^{\rm D}
 &=\{U\in\mathcal P_{\varepsilon,r}:
                     \iota_rU\in\mathcal Q_{\rm mix,\varepsilon}\}.
\end{aligned}
\tag{74.7}
$$

The hard-ball form is $q_{0,\varepsilon}[\iota_rU]
+\int_{G_{\varepsilon,r}}W_\varepsilon|U|^2$ on this domain.
This is the declared Dirichlet exclusion: the zero extension is $H^1$
across the inner wall, so its inner trace is zero wherever that wall has
a trace chart. The original exterior walls retain the mixed-ground form.
The domain is closed, since its zero extensions form the closed subspace
$\{U\in\mathcal Q_{\rm mix,\varepsilon}:U=0\text{ a.e. on }|x-y|\le r\}$.
It is dense in the allowed carrier: smooth functions compactly supported
in the open set $G_{\varepsilon,r}$ are $L^2$-dense, their zero extensions
belong to the domain, and exchange averaging proves the symmetric
assertion. This specifies a closed Dirichlet form without assuming an
identification with another boundary-core closure. Denote its
self-adjoint operator by $\mathsf H_{\varepsilon,r}^{\rm D}\ge-M$.
The two hard-ball discrepancies are

$$
\begin{aligned}
 \Delta^0_{\varepsilon,C}(r)
 &=\|\iota_r(\mathsf H_{\varepsilon,r}^{\rm D}-i)^{-1}\iota_r^*
                                 -K_{\varepsilon,C}\|_{\mathcal B(\mathcal P_\varepsilon)},\\
 \Delta^{\rm a}_{\varepsilon,C}(r)
 &=\|(\mathsf H_{\varepsilon,r}^{\rm D}-i)^{-1}
                    -\iota_r^*K_{\varepsilon,C}\iota_r\|
                                  _{\mathcal B(\mathcal P_{\varepsilon,r})}.
\end{aligned}
\tag{74.8}
$$

The first physical term is a zero-extended resolvent, not the resolvent
of a densely defined self-adjoint operator on the full product.
The allowed-carrier comparator is exactly the compression in (74.8).
Although $\iota_r$ is an isometry, the restricted target lift
$\iota_r^*J_{\varepsilon,2}E$ is only a contraction and is not assumed
isometric.

Zero support radius means a zero multiplier almost everywhere. At zero
radius use the correlation $\chi=1$ and strength $S=0$; the hard model
has Chapter73's zero-radius carrier and mixed form. The assertions below
include these cases with zero overlap loss and zero range quotient.

**Lemma 74.3 (the form estimate at the specified nonreal parameter).**
Let $H\ge-M$ be self-adjoint on a Hilbert space, with closed form $q$.
If $\|z\|\le1$ and $u$ is in its form domain, then

$$
 \|(H-i)^{-1}z\|
 \ge\frac{|\langle z,u\rangle|^2}
 {\sqrt{M^2+1}\,[q[u]+(M+1)\|u\|^2]}.
\tag{74.9}
$$

The quotient is taken only for $u\ne0$; a zero lower bound is automatic.
Indeed put $T=H+M+1\ge1$. For $\lambda\ge-M$,

$$
 \frac{\sqrt{\lambda^2+1}}{\lambda+M+1}\le\sqrt{M^2+1}.
$$

Writing $t=\lambda+M\ge0$, the difference between the squares of the
right and left denominators after cross multiplication is
$M^2t^2+2(M^2+M+1)t\ge0$. Spectral calculus and form Cauchy--Schwarz give

$$
\begin{aligned}
 \langle z,T^{-1}z\rangle
 &\le\|z\|\,\|T^{-1}z\|
 \le\sqrt{M^2+1}\,\|(H-i)^{-1}z\|,\\
 |\langle z,u\rangle|^2
 &\le\langle z,T^{-1}z\rangle\,\|T^{1/2}u\|^2.
\end{aligned}
$$

Their combination proves (74.9). In particular, if a comparison
operator annihilates $z$, (74.9) is a lower bound for its full operator
norm discrepancy from the physical resolvent. $\square$

**Lemma 74.4 (scattering normalization and a local correlation).**
For $h>0$ and radial nonnegative bounded $v$ supported in the radius-$h$ ball,
define, with the physical $\beta$ fixed,

$$
 S(v)=\inf_{1-u\in\mathcal D^{1,2}(\mathbb R^s)}
       \int_{\mathbb R^s}(2\beta|\nabla u|^2+v|u|^2).
\tag{74.10}
$$

Here $\mathcal D^{1,2}$ is the completion of compactly supported smooth
functions in the gradient norm, with its Sobolev
$L^{2s/(s-2)}$ representative. For an ideal hard ball impose $u=0$
a.e. on $B_h$ and omit the potential term outside that constraint.
There is a minimizing radial $u_0$, $0\le u_0\le1$, and a number
$0\le\alpha\le h^{s-2}$ such that

$$
 u_0(r)=1-\frac{\alpha}{r^{s-2}}\quad(r\ge h),\qquad
 S=2\beta(s-2)|\mathbb S^{s-1}|\alpha.
\tag{74.11}
$$

For $L=2h$ the correlation

$$
 \chi_h(r)=
 \begin{cases}u_0(r)/u_0(L),&r<L,\\1,&r\ge L\end{cases}
 \quad\text{satisfies}\quad
 0\le\chi_h\le1,\qquad
 \int(2\beta|\nabla\chi_h|^2+v\chi_h^2)
       =\frac{S}{1-\alpha/L^{s-2}}\le2S.
\tag{74.12}
$$

For the hard ball $\chi_h=0$ on $B_h$, and (74.12) holds with just
its gradient integral. Its exact strength is

$$
 S_{\rm hard}(h)=2\beta(s-2)|\mathbb S^{s-1}|h^{s-2}.
\tag{74.13}
$$

**Proof.** Write $w=1-u$. The gradient term is coercive on
$\mathcal D^{1,2}$; the Sobolev inequality makes restriction to $B_h$
a bounded map into $L^2(B_h)$. Thus the bounded potential term is weakly
lower semicontinuous there. The direct method gives a minimizer; strict
convexity of the gradient norm gives uniqueness. Taking real parts and
truncating $u$ to $[0,1]$ decreases the energy and preserves the affine
space. Rotational invariance and uniqueness give radiality. The weak
Euler equation and its radial version are

$$
 -2\beta\Delta u_0+vu_0=0,\qquad
 (r^{s-1}u_0')'=\frac1{2\beta}r^{s-1}vu_0\ge0.
\tag{74.14}
$$

Finite gradient energy excludes a nonzero flux singularity at zero;
hence $r^{s-1}u_0'$ starts at zero and $u_0$ is increasing. Outside
$B_h$ it is radial harmonic. Membership of $1-u_0$ in the Sobolev
space fixes its constant at infinity to one, giving the first formula
of (74.11). Nonnegativity at $h$ and $u_0\le1$ give the bounds on
$\alpha$. Bounded $v$ also gives $u_0'(r)=O(r)$ near zero from (74.14),
so the boundary term there vanishes. Multiplying (74.14) by $u_0$
and integrating to any $L>h$ gives

$$
 \int_{B_L}(2\beta|\nabla u_0|^2+vu_0^2)
 =2\beta|\mathbb S^{s-1}|L^{s-1}u_0(L)u_0'(L)
 =2\beta(s-2)|\mathbb S^{s-1}|\alpha
                          (1-\alpha/L^{s-2}).
\tag{74.15}
$$

The exterior gradient energy is
$2\beta(s-2)|\mathbb S^{s-1}|\alpha^2/L^{s-2}$.
Adding it proves (74.11). Dividing (74.15) by $u_0(L)^2$ proves
(74.12), since $1-\alpha/(2h)^{s-2}\ge1-2^{2-s}\ge1/2$.
The piecewise correlation is continuous at $L$ and Lipschitz for each
fixed $h,v$, as follows from (74.14) and the explicit exterior formula.

For the hard ball the affine constraint $u=0$ on $B_h$ is nonempty
and closed in the homogeneous Sobolev space, by its local $L^2$
embedding. The same direct method and strict convexity give a unique
minimizer. Rotation invariance makes it radial, and exterior variations
make it harmonic for $r>h$. Its full local $H^1$ representative, zero
inside the ball, has zero exterior trace at $h$. The Sobolev condition
at infinity fixes the other constant. Hence it is zero for $r\le h$
and $1-(h/r)^{s-2}$ for $r>h$. This function belongs to the stated
affine space. Radial integration gives (74.13), and (74.15) has zero
inner boundary term because $u_0(h)=0$. This proves the hard version
of (74.12).
The same hard function is an admissible test in (74.10), so also
$S(v)\le S_{\rm hard}(h)$. $\square$

**Lemma 74.5 (one physical port witness and its allowed restriction).**
Fix any actual port $p$ and put

$$
 k=d_p,\quad N=1+\frac{13}{35}\delta k,\quad
 A_p=(2M+1)N^2+\frac{24}{5}akN,\quad
 c_\varepsilon=\sqrt\delta\,\varepsilon^{-(s-1)/2}.
\tag{74.16}
$$

Use the function $f$ of the proof of Theorem73.3: its atomic value at
$p$ is one, all other atomic values are zero, and on every incident
cable, in distance $t$ from $p$, it is
$b(t)=1-3t^2+2t^3$; it vanishes on other cables. Set
$F_\varepsilon=J_\varepsilon f$ and
$G_\varepsilon(x,y)=F_\varepsilon(x)F_\varepsilon(y)$. Then

$$
\begin{aligned}
 0\le F_\varepsilon\le c_\varepsilon,&\qquad
 \|F_\varepsilon\|_2^2=N,\qquad
 \beta\|\nabla F_\varepsilon\|_2^2=\frac65ak,\\
 \|G_\varepsilon\|_2^2=N^2,&\qquad
 q_{0,\varepsilon}[G_\varepsilon]=\frac{12}{5}akN.
\end{aligned}
\tag{74.17}
$$

Let $Z_p$ be the actual source chamber, so
$|Z_p|=\varepsilon^{s-1}/\delta=c_\varepsilon^{-2}$, and let

$$
 z_\varepsilon=J_{\varepsilon,2}e_{pp}
       =c_\varepsilon^2\mathbf1_{Z_p\times Z_p},\qquad
 \|z_\varepsilon\|=1,
 \qquad K_{\varepsilon,C}z_\varepsilon=0.
\tag{74.18}
$$

For any $0\le\chi\le1$ equal to one for $|x-y|\ge2r$, the product
$U=G_\varepsilon\chi(x-y)$ satisfies

$$
 \langle z_\varepsilon,U\rangle
 \ge\left[1-\frac{2^s\omega_s\delta r^s}
                         {\varepsilon^{s-1}}\right]_+,
 \qquad \|U\|^2\le N^2,
\tag{74.19}
$$

provided it is the nonnegative product under consideration. Here
$\omega_s=|B_1\subset\mathbb R^s|$ and $[t]_+=\max\{t,0\}$.
If $\chi=0$ on $B_r$ and the product is in
$\mathcal Q_{\rm mix,\varepsilon}$, its allowed restriction lies in
$\mathcal Q_{\varepsilon,r}^{\rm D}$. Put
$z_{\varepsilon,r}=\iota_r^*z_\varepsilon$. Then

$$
 \|z_{\varepsilon,r}\|\le1,\qquad
 (\iota_r^*K_{\varepsilon,C}\iota_r)z_{\varepsilon,r}=0,\qquad
 \langle z_{\varepsilon,r},\iota_r^*U\rangle
                       =\langle z_\varepsilon,U\rangle.
\tag{74.20}
$$

**Proof.** Direct gluing gives $F_\varepsilon\in H^1(\Omega)$:
its constant chamber and longitudinal cylinder traces match, and it
vanishes on all ground half-chambers and grounded cuts. The integrals
$\int_0^1 b^2=13/35$ and $\int_0^1|b'|^2=6/5$, with the actual
cross-sectional measure $\varepsilon^{s-1}$, prove (74.17).
The tensor product is symmetric and has both grounded traces zero.
No operator-domain regularity of the physical lift is needed.
Equation (73.6) gives (74.18), since $E^*e_{pp}=0$.
On $Z_p\times Z_p$ the product $G_\varepsilon$ equals
$c_\varepsilon^2$. For each $x\in Z_p$, at most
$\omega_s(2r)^s$ of the $y$-volume can lose any overlap. Thus the
loss is at most
$c_\varepsilon^4|Z_p|\omega_s(2r)^s
=2^s\omega_s\delta r^s/\varepsilon^{s-1}$. The integrand is
nonnegative, proving (74.19).

For the hard carrier the asserted membership is exactly the definition
(74.7). Moreover $\iota_rz_{\varepsilon,r}$ is still supported
entirely in $Z_p\times Z_p$. By (73.6) its $J_{\varepsilon,2}^*$
image is a scalar multiple of $e_{pp}$, even though the restriction is
not constant on that chamber product. Consequently
$K_{\varepsilon,C}\iota_rz_{\varepsilon,r}=0$.
This proves (74.20) for the actual compressed comparator, without an
isometry claim for the restricted lift. $\square$

**Theorem 74.6 (source-normalized scattering-strength obstruction).**
In the soft scattering model define $S_\varepsilon=S(v_\varepsilon)$
by (74.10) and put

$$
 \Gamma_\varepsilon=\frac{S_\varepsilon}{\varepsilon^{s-1}},
 \qquad b_\varepsilon(r)=
       \left[1-\frac{2^s\omega_s\delta r^s}
                          {\varepsilon^{s-1}}\right]_+.
\tag{74.21}
$$

For every actual port $p$, every comparator $C$ in (74.2), every
admissible $v_\varepsilon,W_\varepsilon$, and every sufficiently small
$\varepsilon$ for which the fixed geometry is defined,

$$
 \Delta_{\varepsilon,C}
 \ge\frac{b_\varepsilon(h_\varepsilon)^2}
 {\sqrt{M^2+1}\,[A_p+4\delta N\Gamma_\varepsilon]}.
\tag{74.22}
$$

The identical bound holds for each of
$\Delta^0_{\varepsilon,C}(h_\varepsilon)$ and
$\Delta^{\rm a}_{\varepsilon,C}(h_\varepsilon)$ for an ideal hard ball,
using $S_\varepsilon=S_{\rm hard}(h_\varepsilon)$.

**Proof.** Take the actual physical function
$U_\varepsilon=G_\varepsilon\chi_{h_\varepsilon}(x-y)$ from
Lemma74.4. Its correlation is Lipschitz for each $\varepsilon$;
multiplication and the matched ground traces put it in precisely the
soft form domain. The elementary derivative inequality
$|\xi+\eta|^2\le2|\xi|^2+2|\eta|^2$ gives

$$
\begin{aligned}
 q_{0,\varepsilon}[G_\varepsilon\chi]
       +\int v_\varepsilon G_\varepsilon^2\chi^2
 &\le2q_{0,\varepsilon}[G_\varepsilon]
       +\int_{\Omega^2}G_\varepsilon^2
            (4\beta|\nabla\chi(x-y)|^2
                           +v_\varepsilon(x-y)\chi(x-y)^2)\\
 &\le\frac{24}{5}akN
       +2c_\varepsilon^2N
             \int_{\mathbb R^s}(2\beta|\nabla\chi|^2
                                      +v_\varepsilon\chi^2)\\
 &\le\frac{24}{5}akN+4\delta N\Gamma_\varepsilon.
\end{aligned}
\tag{74.23}
$$

In the first line the gradient inside the last integral is the
relative-variable gradient: the two physical coordinate gradients of
$\chi(x-y)$ have the same magnitude. For any nonnegative relative
integrand $e$, the estimate used in the second line is

$$
 \int_{\Omega^2}F_\varepsilon(x)^2F_\varepsilon(y)^2e(x-y)
 \le c_\varepsilon^2\|F_\varepsilon\|_2^2
                                      \int_{\mathbb R^s}e.
\tag{74.24}
$$

It follows by fixing $x$, bounding $F_\varepsilon(y)^2$ by
$c_\varepsilon^2$, and enlarging only that relative integral to
$\mathbb R^s$. Thus no fixed-domain limit, extension of a Neumann
state, or trap theorem is implicit in (74.23).
Since $W_\varepsilon\le M$ and $\|U_\varepsilon\|^2\le N^2$,
(74.23) implies

$$
 q_\varepsilon[U_\varepsilon]+(M+1)\|U_\varepsilon\|^2
                   \le A_p+4\delta N\Gamma_\varepsilon.
\tag{74.25}
$$

Apply Lemma74.3 to $z_\varepsilon$ and this trial function, and use
(74.18)--(74.19). The comparator kills the input, so this proves the
full norm bound (74.22).

For an ideal hard ball the same function is zero for $|x-y|\le h$,
and is an $H^1$ zero extension with both grounded traces zero.
Its allowed restriction therefore belongs to the declared Dirichlet
form domain (74.7); this proves the required membership directly.
Use the hard version of (74.12) in (74.23), omitting the potential term.
On the allowed carrier, Lemma74.3 and (74.20) prove the bound for
$\Delta^{\rm a}$. On the full carrier, apply the allowed resolvent to
$\iota_h^*z_\varepsilon$ and extend the output by zero; meanwhile
$K_{\varepsilon,C}z_\varepsilon=0$ and $\|z_\varepsilon\|=1$.
The same estimate proves the bound for $\Delta^0$. Both comparisons
use the actual hard carrier and the same Dirichlet form. $\square$

**Theorem 74.7 (broader support-range obstruction).** In the separate
range model, with no further condition on $R_\varepsilon\to0$, put

$$
 \tau_\varepsilon=\frac{R_\varepsilon^{s-2}}{\varepsilon^{s-1}},
 \qquad B_p=2^{s+2}a\omega_sN.
\tag{74.26}
$$

For every $C$ in (74.2) the full soft discrepancy obeys

$$
 \Delta_{\varepsilon,C}
 \ge\frac{b_\varepsilon(R_\varepsilon)^2}
                  {\sqrt{M^2+1}\,[A_p+B_p\tau_\varepsilon]}.
\tag{74.27}
$$

The same bound holds for each hard-ball discrepancy in (74.8) at
$r=R_\varepsilon$. Consequently, along any subsequence on which
$\tau_\varepsilon\le T<\infty$, each applicable discrepancy satisfies

$$
 \liminf\Delta
 \ge\frac1{\sqrt{M^2+1}\,[A_p+2^{s+2}a\omega_sNT]}>0.
\tag{74.28}
$$

**Proof.** Use the radial Lipschitz cutoff, without a scattering
hypothesis on the actual potential,

$$
 \chi_R(r)=
 \begin{cases}
 0,&|r|\le R,\\
 (|r|-R)/R,&R<|r|<2R,\\
 1,&|r|\ge2R.
 \end{cases}
 \qquad
 \int_{\mathbb R^s}|\nabla\chi_R|^2
                      \le2^s\omega_sR^{s-2}.
\tag{74.29}
$$

The product $U=G_\varepsilon\chi_R(x-y)$ belongs to the mixed form
domain and $\int V_\varepsilon|U|^2=0$. Hence it belongs to the exact
natural sum domain (74.5), regardless of the permitted singularity or
height of $V_\varepsilon$. The same zero extension proves its hard
Dirichlet membership. The derivative estimate and (74.24) now give

$$
 q_{0,\varepsilon}[U]
 \le\frac{24}{5}akN
        +4\beta c_\varepsilon^2N\int|\nabla\chi_R|^2
 \le\frac{24}{5}akN+B_p\tau_\varepsilon.
\tag{74.30}
$$

Adding the shifted bounded-potential term gives the denominator of
(74.27). Lemma74.3 with (74.19), and (74.20) in the hard case, proves
all three assertions about finite $\varepsilon$ exactly as above.
On the specified subsequence the overlap loss obeys

$$
 1-b_\varepsilon(R_\varepsilon)
 \le2^s\omega_s\delta\,\tau_\varepsilon R_\varepsilon^2
 \longrightarrow0.
$$

Using $\tau_\varepsilon\le T$ in the denominator proves (74.28).
In particular, this step needs only $R_\varepsilon\to0$ and the
subsequence bound, not $R_\varepsilon=o(\varepsilon)$. $\square$

**Corollary 74.8 (necessary strength, range and finite-error conditions).**
Within the soft scattering model, convergence of (74.6) to zero for
even one of the unchanged comparators requires
$\Gamma_\varepsilon\to\infty$. The same is true for convergence of
either hard-ball discrepancy at radius $h_\varepsilon=o(\varepsilon)$.
Indeed
$h_\varepsilon^s/\varepsilon^{s-1}
=\varepsilon(h_\varepsilon/\varepsilon)^s\to0$;
if $\Gamma_\varepsilon$ does not tend to infinity, a bounded
subsequence in (74.22) gives a strictly positive lower limit.
Within the broader range model, or its hard-ball version, convergence
requires $\tau_\varepsilon\to\infty$, by (74.28).

For a finite error tolerance $\eta>0$, each applicable scattering
comparison satisfying $\Delta\le\eta$ must satisfy

$$
 \Gamma_\varepsilon\ge\frac1{4\delta N}
 \left[\frac{b_\varepsilon(h_\varepsilon)^2}
                         {\sqrt{M^2+1}\,\eta}-A_p\right]_+.
\tag{74.31}
$$

Each applicable range comparison satisfying $\Delta\le\eta$ must
likewise satisfy

$$
 \tau_\varepsilon\ge\frac1{B_p}
 \left[\frac{b_\varepsilon(R_\varepsilon)^2}
                         {\sqrt{M^2+1}\,\eta}-A_p\right]_+.
\tag{74.32}
$$

These follow by rearranging the respective positive denominators;
when the overlap factor is zero they give only the trivial condition.
They hold separately for every port, without any change of comparator.

In $s=3$, $\alpha$ in (74.11) is the scattering length $\ell$ with
the relative kinetic normalization $2\beta$. Thus

$$
 S=8\pi\beta\ell,\qquad
 \Gamma_\varepsilon=8\pi\beta
                 \frac{\ell_\varepsilon}{\varepsilon^2},\qquad
 \frac{\ell_\varepsilon}{\varepsilon^2}\longrightarrow\infty
                       \quad\hbox{is necessary}.
\tag{74.33}
$$

For an ideal hard ball $\ell=h$, and in every fixed $s\ge3$ its
strength is precisely (74.13). Since $S(v)\le S_{\rm hard}(h)$,
strength divergence also entails divergence of the corresponding
normalized support range in the radial model. The converse is not
implied. These are necessary obstructions; they establish neither a
sufficient convergence criterion nor a sharp threshold. All assertions
have fixed $D,\delta,a,s,M$ and fixed geometry. There is no
source-growth, $\delta\to0$, growing-$M$, or dimension-uniform assertion.

**Proposition 74.9 (growing height and normalized range can have vanishing
strength).** In $s=3$, for any fixed $\beta>0$, take

$$
 h_\varepsilon=\varepsilon^{3/2},\qquad
 v_\varepsilon(r)=\varepsilon^{-1}
                          \mathbf1_{\{|r|\le h_\varepsilon\}}.
\tag{74.34}
$$

The height tends to infinity and
$h_\varepsilon/\varepsilon^2=\varepsilon^{-1/2}\to\infty$, while
$h_\varepsilon/\varepsilon=\varepsilon^{1/2}\to0$.
Nevertheless

$$
 \ell_\varepsilon
   =\frac{\varepsilon^{7/2}}{6\beta}(1+O(\varepsilon^2)),
 \qquad
 \Gamma_\varepsilon
   =\frac{4\pi}{3}\varepsilon^{3/2}(1+O(\varepsilon^2))
       \longrightarrow0.
\tag{74.35}
$$

Consequently Theorem74.6 obstructs full resolvent convergence for this
model for every allowed $W_\varepsilon$, separately for all three
comparators. The growing range here is the ratio to the
$\varepsilon^2$ scale; the actual support radius tends to zero.

**Proof.** For a constant barrier of height $H>0$ and radius $h$, let
$\kappa=\sqrt{H/(2\beta)}$. Solving (74.14) in three dimensions with
finite value at zero gives the candidate

$$
 u_0(r)=
 \begin{cases}
 \displaystyle\frac{\sinh(\kappa r)}
                   {\kappa r\cosh(\kappa h)},&0<r\le h,\\[4pt]
 1-\ell/r,&r\ge h,
 \end{cases}
 \quad u_0(0)=\frac1{\cosh(\kappa h)},\qquad
 \ell=h-\frac{\tanh(\kappa h)}{\kappa}.
\tag{74.36}
$$

The interior solves $u_0''+2u_0'/r=\kappa^2u_0$.
At $h$ its value is $\tanh(\kappa h)/(\kappa h)=1-\ell/h$
and its derivative is
$1/h-\tanh(\kappa h)/(\kappa h^2)=\ell/h^2$.
Thus value and flux match, the weak equation holds across $h$, and
$1-u_0\in\mathcal D^{1,2}$. Uniqueness in Lemma74.4 identifies it
with the variational minimizer, not merely a radial trial estimate.
For (74.34), $\kappa h=\varepsilon/\sqrt{2\beta}$.
The Taylor expansion with its analytic remainder,
$\tanh z=z-z^3/3+O(z^5)$ as $z\to0$, gives
$\ell=Hh^3/(6\beta)(1+O(Hh^2/\beta))$.
Substituting $H=\varepsilon^{-1}$ and $h=\varepsilon^{3/2}$,
and then using (74.33), proves (74.35). This analytical computation
also agrees with the elementary upper bound
$S(v)\le\int v=(4\pi/3)\varepsilon^{7/2}$ from the admissible
constant function $u=1$. No numerical experiment or trap convergence
theorem is a premise of the network conclusion. $\square$

**Definition 74.10 (primary reuse, exact scope and remaining obligations).**
Robert Seiringer and Jun Yin,
[*The Lieb--Liniger Model as a Limit of Dilute Bosons in Three Dimensions*,
arXiv:0709.4022v1](https://arxiv.org/pdf/0709.4022v1), Section3, PDF
pp7--9, uses distance-dependent scattering correlations, normalized at a
finite cutoff, with norm-loss and energy estimates. That local method is
mature supplier mathematics. Section2, Theorems1--2 and Corollaries1--2,
PDF pp3--5, and the norm-resolvent paragraph after Corollary2 concern fixed
particle number and longitudinal scale with separable transverse and
longitudinal confinement. Their effective coupling is
$8\pi a_{\rm SY}\|b_{\rm SY}\|_4^4/r_{\rm SY}^2$; the stated limit
includes infinite coupling while retaining the separation
$a_{\rm SY}/r_{\rm SY}\to0$. The paper permits hard spheres and discusses
interval and transverse-boundary variants on PDF p6. These results do
not supply an interacting massive-port network theorem, either pair
law of (74.3), or a native operation. No eigenfunction-error formula from
its equation(2.8) is used here.

The physical geometry, exact chamber volumes, original identifications
and grounded form are the already supplied72.1--72.10 and73.2--73.3;
the entire free limit and fixed-thickness coincidence-capacity result
are not reproved or extended to interactions. Closed-form representation
is used in the same scope as the Teschl supplier in Definition68.7.
The Sobolev Dirichlet principle, product differentiation, spectral
calculus and Cauchy--Schwarz are classical. Lemma74.4 proves the required
general-$s$ normalization directly. The additional ordinary repo-derived
results are the source-normalized full-carrier bounds (74.22),
(74.27)--(74.28), their actual hard-carrier versions, and their necessary
precision consequences. Scoped overlap with the supplied boundary
continuations and relation geometry gives no world-priority claim.
A witness lower-bounds the norm on the entire declared carrier; it does
not replace that carrier or the literal target by a harmonic,
atomic-only, occupation-label or test-subclass surrogate. The radial
scattering-strength scope and the broader nonradial support-range scope
remain distinct. Neither result asserts a generic fixed-domain
obstruction or a sufficient interacting realization.

Every obligation of72.13,66.10,67.11,68.7 and Chapter73's final scope
remains in force. Retain the full source with every literal label,
bracket, left/right order and distinct occurrence, immutable INITIAL,
one fixed original cap, source-independent original initialization,
complete supplied contexts, whole candidates and original guards,
every acceptance and refusal, original Read, absorbing Stop and every
actually acquired record. The original actor's arbitrary, unbounded or
possibly zero $a$, its untagged radius-$7/25$ $b$, destructive actions
and joint history-dependent errors are distinct from the fixed positive
commissioned $a$ here. No mathematical potential, chamber identification
or cutoff acquires a native source service or changes a legal operation.
Actual graft changes of root, degrees and field values, whole-rho and
distinct Left/Right operations keep their original correspondence duties.
The prescribed planar metric and grounding-line problem of72.13 remains
unresolved, with its exact lengths, clearance and port margins.

All field modes and spectators, unknown particle/field/auxiliary
correlations, complete norms, common reference and actual clock remain.
Unknown-state ingress and recovery, original Read/Stop covariance,
operation-preserving and metric-preserving maps, Hilbert-valued domain
and dynamic bridges, preparation, harmonic/projection control, retained
complements and both cross blocks remain independent requirements.
There is no supplied reset, cloning, independent resampling,
calibrated-state re-preparation or exact-limit Read. An encoded or
separate carrier still owes all recovery, read, operation and dynamic
relations; an abstract Hilbert-space isomorphism or static Green fit
supplies none of them. The common $\Pi$ of63.13 retains its full-vector
and spanning, common-zero, whole quadratic-distance/positive-semidefinite
Gram, at least two independent directions, alternating bilinear
exact-area/Jacobi, actual orthonormal-probe, finite binary-calibration
and hidden-kernel-preserving generator hypotheses.

The distinct acquisition contracts remain separate. Section57's
immutable composition-promised endpoint acquisition retains depth caps,
common source-independent initialization, actual query/reply histories,
correct finite stopping on every promised positive and negative source,
and distinct actual-address fees without an old-source archive. The
paid positive-root archive/nonadvancing-cut acquisition retains its exact
port, finite stopping and decoding, protected records after refusal or
closure, aligned actual generation, trusted markers, no unrecorded
source change, closed strong ports and actual write/protect/retain/query
rights. Every reply-affecting retained source influence belongs in its
service price. The phase-coherent full-tail acquisition retains its
once-sampled-depth actual Read process and paid stopped transcript.
Their radii, state counts, update rules and clocks are not transferred
to this continuum model.

The unresolved spatial realization still owes isotropic local physical
mediators for both complete common and killed laws with the unchanged
one-body field, genuine switching, packing, transverse and exterior
control, leakage and collision control, reference preparation and clock
calibration. Every construction, acquisition, preparation,
field/compensation/stiffness installation, control, service, production,
storage, hold, retention, maintenance, precision and total lifetime
resource remains to be supplied, together with the original joint error
guarantees and actual finite execution certificates. In particular growing barrier height,
shrinking range, increasing scattering strength and form admissibility
are mathematical parameters, not acquired controls or apparatus prices.
The fixed-$s\ge3$ obstructions select no unique dimension and prove no
global physical impossibility. They supply no positive interacting
realization, physical validation, fresh Lean/kernel result, independent
prior or model-diversity certificate, or completion of the sustained
why-three/source/native/field/acquisition/resource objective.

## 74.99 追加锚（本行以下为增补区）
## 75. Chamber-scale exclusion and the complete fixed-source hard-core limit

**Definition 75.1 (fixed source, geometry and literal target).** Fix every item of Definition72.1: one authentic nonempty finite full binary source $D$, its actual occurrence identities and inherited seams, its two distinct unit grounded stubs at each current leaf, commissioned $a>0$, $0<\delta\le1$, one integer $s\ge3$, the positive reference volumes of the distinct ground chambers, and one chosen separated assembly of72.3–72.6. Fix also the original commissioned $g>0$ and $\nu\ge0$. All these data remain fixed as $\varepsilon\downarrow0$. Write

$$
d=|D|,\qquad r_\varepsilon=\varepsilon^{(s-1)/s},\qquad
\beta=\frac a\delta,\qquad \lambda=3-2\sqrt2.
\tag{75.1}
$$

Let $X_D$ be exactly Definition64.5's compact unit-cable tree, including its distinct ground tips, with path metric $d_X$ and measure $\mu_\delta$. A ground tip has no atomic mass. Put $\mathcal H^{\rm fr}=\mathcal H_2^{\rm fr}$, $\mathcal Q^{\rm fr}=\mathcal Q_2^{\rm fr}$, and let $B$ and $q^{\rm fr}$ be precisely the complete free product operator and form of73.1–73.2. Let $\mathcal K=\mathcal K_{D,2}^{\rm hc}$ and $\mathcal Q^{\rm hc}=\mathcal Q_{D,2}$ be the unchanged literal target. The isometry $E:\mathcal K\to\mathcal H^{\rm fr}$ identifies every slice and cell coordinate and inserts zero at every atomic $(p,p)$; its adjoint deletes those atomic coordinates. The exact domain identification supplied by(73.8) is

$$
E\mathcal Q^{\rm hc}
=\{F\in\mathcal Q^{\rm fr}:F_{pp}=0\ (p\in D),\quad
       \operatorname{Tr}_{x=y}F_{ee}=0\ (e\in\mathcal E_D)\}.
\tag{75.2}
$$

This is an equality of complete form domains. The two triangles of a same-cable square glue to an $H^1$ square because their diagonal traces are both zero. Every different-cable rectangle remains. Cell boundary traces equal the appropriate atom/cable slices, whose endpoints equal the atomic pair coordinates. Grounded traces vanish in either coordinate. At a collision port the missing atomic value is zero, so every incident collision slice ends at zero, including approaches along different cables. No point trace at a rectangle corner is imposed.

Before exchange restriction the norm and kinetic form are

$$
\begin{aligned}
\|F\|^2={}&\sum_{p\ne q}|F_{pq}|^2
 +\delta\sum_{p,e}\bigl(\|F_{pe}\|_2^2+\|F_{ep}\|_2^2\bigr)
 +\delta^2\sum_{e,f}\|F_{ef}\|_2^2,\\
a k_{\delta,2}[F]={}&a\sum_{e,q}\|\partial_xF_{eq}\|_2^2
 +a\sum_{p,f}\|\partial_yF_{pf}\|_2^2
 +a\delta\sum_{e,f}\int\bigl(|\partial_xF_{ef}|^2+|\partial_yF_{ef}|^2\bigr).
\end{aligned}
\tag{75.3}
$$

The same-cable integrals include both triangles. There are $d(d-1)$ ordered distinct atomic coordinates, $4d^2$ mixed slices and $4d^2$ cells, with each of the $2d$ same-cable cells dissected. Symmetry restricts these spaces without an additional factor or ordering sign. Every interval and cell keeps its entire infinite-dimensional space. In particular the singleton source retains a nonzero continuum two-position target even though it has no distinct atomic pair.

The three target operators, considered separately, are

$$
\begin{aligned}
C_0&=A_{\delta,D,2},\quad U_0=0,\qquad
C_\diamond=\mathcal T^\diamond_{\delta,D,2}=C_0+U_\diamond,
\quad \diamond\in\{\mathrm c,\mathrm k\},\\
U_\diamond(x,y)&=-g\bigl(\phi_A(x)+\phi_A(y)\bigr)
-\nu\mathbf1_{x=p,y=q\in D,\ p\ne q}G_D^\diamond(p,q).
\end{aligned}
\tag{75.4}
$$

Here $\phi(p)=2^{-|p|}$ and $\phi_A$ is zero on open cables. For every $D$ the complete original prescriptions are

$$
G_D^{\rm c}(p,q)=\frac23\,2^{-d(p,q)}+\frac13\,2^{-(|p|+|q|)},
\qquad G_D^{\rm k}(p,q)=\langle e_p,L_D^{-1}e_q\rangle.
\tag{75.5}
$$

In(75.5), $d(p,q)=|p|+|q|-2|p\wedge q|$, with $p\wedge q$ the longest common occurrence prefix. The first expression is the restriction of the same infinite source kernel $L^{-1}$, not a refitted finite kernel. The source matrix is $(L_D)_{pq}=d_p\mathbf1_{p=q}-\mathbf1_{p\sim q}$, where $p\sim q$ is an inherited seam, $d_o=2$ and every other $d_p=3$; these diagonals retain all exterior terms. Equivalently(67.2) gives $G_D^{\rm c}=(L_D-P_{\operatorname{Leaf}(D)})^{-1}$ and $G_D^{\rm k}=L_D^{-1}$. The bounds $\lambda I\le F_D^\diamond\le6I$ and $0<G_D^\diamond(p,q)\le\lambda^{-1}$ are the already supplied source bounds. Killing changes the pair prescription and leaves the original one-body field $\phi$ unchanged.

**Definition 75.2 (physical carriers, exact maps and adjoints).** Use $\Omega_\varepsilon=\Omega_\varepsilon^+$ of72.5 and $\mathcal P_\varepsilon=L^2_{\rm sym}(\Omega_\varepsilon^2)$. Its mixed-ground form domain $\mathcal Q_{{\rm mix},\varepsilon}$ is exactly(73.5): symmetric $H^1$ functions with zero trace on both grounded product faces, with no essential condition on the exterior Neumann walls. The free form is

$$
q_{0,\varepsilon}[u]=\beta\int_{\Omega_\varepsilon^2}
                 (|\nabla_xu|^2+|\nabla_yu|^2).
\tag{75.6}
$$

Denote its operator by $B_\varepsilon$. Write $J=J_{\varepsilon,2}$ for the actual isometry of73.6, not a harmonic calibration. For a source port let $Z_p^\varepsilon$ be its chamber, and for a cable let $Z_e^\varepsilon(x)$ be its cross-section at longitudinal coordinate $x$. Put $c_\varepsilon=\sqrt\delta\,\varepsilon^{-(s-1)/2}$. On the ordered chamber/chamber, chamber/cylinder, cylinder/chamber and cylinder/cylinder products, respectively, $JF$ equals

$$
c_\varepsilon^2F_{pq},\qquad c_\varepsilon^2F_{pe}(y),\qquad
c_\varepsilon^2F_{ep}(x),\qquad c_\varepsilon^2F_{ef}(x,y).
\tag{75.7}
$$

It is zero if either coordinate lies in a ground half-chamber. The adjoint on all physical Hilbert data is

$$
(J^*u)_{\alpha\gamma}
 =b_\alpha b_\gamma\int_{Z_\alpha^\varepsilon\times Z_\gamma^\varepsilon}u,
\qquad b_p=c_\varepsilon,\quad b_e=c_\varepsilon/\delta.
\tag{75.8}
$$

Cable longitudinal variables are not integrated in this formula. The volumes $|Z_p^\varepsilon|=\varepsilon^{s-1}/\delta$ and $|Z_e^\varepsilon(x)|=\varepsilon^{s-1}$ give $J^*J=I$ with precisely the weights in(73.1). Set $L_\varepsilon=JE$, so $L_\varepsilon^*L_\varepsilon=I$ and $L_\varepsilon^*=E^*J^*$. Both $J$ and $L_\varepsilon$ have proper range in the full physical space: nonconstant chamber and transverse modes and ground half-chamber functions remain there.

For a radius $R_\varepsilon>0$ put, exactly as in74.7,

$$
\begin{aligned}
G_{\varepsilon,R}&=\{(x,y)\in\Omega_\varepsilon^2:|x-y|>R_\varepsilon\},
&\mathcal P_{\varepsilon,R}&=L^2_{\rm sym}(G_{\varepsilon,R}),\\
\iota_\varepsilon&:\mathcal P_{\varepsilon,R}\to\mathcal P_\varepsilon,
&\iota_\varepsilon u&=\text{zero extension},\\
\mathcal Q_{\varepsilon,R}^{\rm D}
 &=\{u\in\mathcal P_{\varepsilon,R}:\iota_\varepsilon u
                                  \in\mathcal Q_{{\rm mix},\varepsilon}\}.
\end{aligned}
\tag{75.9}
$$

The adjoint $\iota_\varepsilon^*$ is restriction to the allowed set. The zero extensions in this domain are exactly the mixed-ground $H^1$ functions vanishing almost everywhere on $|x-y|\le R_\varepsilon$. Thus this is Dirichlet exclusion across the inner wall in its trace charts, retaining the original exterior and grounded conditions. Chapter74 supplies its closedness and density on the allowed carrier; no global $H^2$ regularity or alternative boundary-core identification is assumed. The allowed target lift and its adjoint are exactly

$$
T_\varepsilon=\iota_\varepsilon^*L_\varepsilon,\qquad
T_\varepsilon^*=L_\varepsilon^*\iota_\varepsilon.
\tag{75.10}
$$

This lift is a contraction. Its isometry is neither assumed nor needed.

**Definition 75.3 (explicit additional installation hypotheses).** Install the Dirichlet domain(75.9) and, separately for each prescription, the following real bounded multiplication operator. With $\chi_p^\varepsilon=\mathbf1_{Z_p^\varepsilon}$ set

$$
\begin{aligned}
\Phi_\varepsilon(x)&=\sum_{p\in D}2^{-|p|}\chi_p^\varepsilon(x),
&W_{\varepsilon,0}&=0,\\
W_{\varepsilon,\diamond}(x,y)
 &=-g\bigl(\Phi_\varepsilon(x)+\Phi_\varepsilon(y)\bigr)
 -\nu\sum_{p\ne q}G_D^\diamond(p,q)
                         \chi_p^\varepsilon(x)\chi_q^\varepsilon(y),
&M&=2g+\nu/\lambda.
\end{aligned}
\tag{75.11}
$$

The one-body field is zero on every cylinder and ground half-chamber. An ordered distinct chamber pair activates exactly one term of the ordered sum, without a factor two. Hence every $W_{\varepsilon,C}$ is exchange symmetric and has norm at most $M$, independently of $\varepsilon$. Let $H_{\varepsilon,R,C}^{\rm D}$ be the operator on $\mathcal P_{\varepsilon,R}$ of

$$
h_{\varepsilon,C}[u]=q_{0,\varepsilon}[\iota_\varepsilon u]
       +\int_{G_{\varepsilon,R}}W_{\varepsilon,C}|u|^2,
\qquad u\in\mathcal Q_{\varepsilon,R}^{\rm D}.
\tag{75.12}
$$

It is self-adjoint and bounded below by $-M$, by the closed form of74.2 and bounded perturbation. To specify the actual operator domains without any corner regularity assumption, polarize the forms and use

$$
\begin{aligned}
\operatorname{Dom}H_{\varepsilon,R,C}^{\rm D}
&=\{u\in\mathcal Q_{\varepsilon,R}^{\rm D}:\exists w\in\mathcal P_{\varepsilon,R},\quad
h_{\varepsilon,C}(u,v)=\langle w,v\rangle
\text{ for every }v\in\mathcal Q_{\varepsilon,R}^{\rm D}\},\\
\operatorname{Dom}C
&=\{f\in\mathcal Q^{\rm hc}:\exists h\in\mathcal K,\quad
q_C(f,v)=\langle h,v\rangle
\text{ for every }v\in\mathcal Q^{\rm hc}\},
\end{aligned}
$$

with outputs $w$ and $h$, respectively, where $q_C=a k_{\delta,2}+\langle U_C\,\cdot,\,\cdot\rangle$. Density makes those outputs unique. These are exact weak operator domains, retaining the natural exterior conditions and every stipulated essential trace; no global piecewise-$H^2$ description is substituted. Bounded multiplication leaves the corresponding kinetic operator domains unchanged, since its contribution can be moved to the representing Hilbert vector in these identities. These exact step multipliers and the exclusion are added mathematical installation hypotheses. No native force, acquired switch, local field mediator, source service or physical control follows from declaring them. The common and killed forms are distinct prescriptions on one common source and geometry.

**Theorem 75.4 (the chamber-covering assertion and its fixed-positive-radius strengthening).** Under75.1–75.3, choose any fixed $\kappa>0$ and set

$$
R_\varepsilon=\kappa r_\varepsilon.
\tag{75.13}
$$

For every fixed compact $K\subset\mathbb C\setminus\mathbb R$, define

$$
\begin{aligned}
K_{\varepsilon,C}(z)&=L_\varepsilon(C-z)^{-1}L_\varepsilon^*,\\
D_{\varepsilon,C}^0(z)
 &=\big\|\iota_\varepsilon(H_{\varepsilon,R,C}^{\rm D}-z)^{-1}
                   \iota_\varepsilon^*-K_{\varepsilon,C}(z)\big\|
                                     _{\mathcal B(\mathcal P_\varepsilon)},\\
D_{\varepsilon,C}^{\rm a}(z)
 &=\big\|(H_{\varepsilon,R,C}^{\rm D}-z)^{-1}
                   -T_\varepsilon(C-z)^{-1}T_\varepsilon^*\big\|
                                  _{\mathcal B(\mathcal P_{\varepsilon,R})}.
\end{aligned}
\tag{75.14}
$$

Then

$$
\max_{C\in\{C_0,C_{\rm c},C_{\rm k}\}}\ \sup_{z\in K}
D_{\varepsilon,C}^0(z)\longrightarrow0,\qquad
\max_{C\in\{C_0,C_{\rm c},C_{\rm k}\}}\ \sup_{z\in K}
D_{\varepsilon,C}^{\rm a}(z)\longrightarrow0.
\tag{75.15}
$$

At $z=i$ these are literally both hard-carrier comparisons(74.8), for the full unchanged Definition64.5 target. The first physical term is a zero-extended resolvent, not the resolvent of a densely defined full-product operator. For every tolerance $\eta>0$, one $\varepsilon_0$ works for all three prescriptions, all $z\in K$ and every forcing vector of norm at most one on the corresponding actual carrier.

In particular the original chamber-covering hypothesis suffices. Indeed72.4–72.6 give constants $0<\ell_p\le M_p<\infty$, independent of small $\varepsilon$, such that

$$
Z_p^\varepsilon=b_p^\varepsilon+r_\varepsilon K_p(\varepsilon^{1/s}),
\qquad B_{\ell_p}(0)\subset K_p(\varepsilon^{1/s})\subset B_{M_p}(0).
\tag{75.16}
$$

Thus $B_D=\max_p2M_p$ bounds every chamber diameter divided by $r_\varepsilon$. Any fixed $\kappa>B_D$ excludes each entire $Z_p^\varepsilon\times Z_p^\varepsilon$. The theorem also holds for every fixed $0<\kappa\le B_D$ on these same uniformly nondegenerate chambers. This does not assert uniformity as $\kappa\downarrow0$ or for growing sources, shrinking $\delta$, increasing dimension or changing reference geometry. The proof is75.5–75.10.

**Lemma 75.5 (full physical compactness and the free lower form bound).** Suppose $\varepsilon_j\downarrow0$ and $u_j\in\mathcal Q_{{\rm mix},\varepsilon_j}$ satisfy

$$
\sup_j\bigl(q_{0,\varepsilon_j}[u_j]+\|u_j\|^2\bigr)<\infty.
\tag{75.17}
$$

There is a subsequence and $F\in\mathcal Q^{\rm fr}$ with

$$
\|u_j-J_{\varepsilon_j,2}F\|\longrightarrow0,
\qquad q^{\rm fr}[F]\le\liminf_j q_{0,\varepsilon_j}[u_j].
\tag{75.18}
$$

The conclusion concerns the entire physical norm, including the proper-range complement.

**Proof.** Reuse73.2, including the negative resolvent convergence established in its proof:

$$
\eta_\varepsilon=
\big\|(B_\varepsilon+1)^{-1}-J(B+1)^{-1}J^*\big\|\longrightarrow0.
\tag{75.19}
$$

The complete free $B$ has compact resolvent by73.4; equivalently its finite atomic, interval and rectangle form embedding is compact. Let $P_m$ be finite spectral projections exhausting its eigenbasis, and let $\Lambda_m\to\infty$ bound the omitted eigenvalues from below. Set $Q_{\varepsilon,m}=I-JP_mJ^*$. For $v\in\mathcal Q_{{\rm mix},\varepsilon}$ write $v=(B_\varepsilon+1)^{-1/2}w$, with $\|w\|^2=q_{0,\varepsilon}[v]+\|v\|^2$. Compression of(75.19) gives

$$
\begin{aligned}
\|Q_{\varepsilon,m}v\|^2
&\le \big\|Q_{\varepsilon,m}(B_\varepsilon+1)^{-1}
                         Q_{\varepsilon,m}\big\|\,\|w\|^2\\
&\le \bigl(\eta_\varepsilon+(1+\Lambda_m)^{-1}\bigr)
                       \bigl(q_{0,\varepsilon}[v]+\|v\|^2\bigr).
\end{aligned}
\tag{75.20}
$$

For each fixed $m$, the bounded vectors $P_mJ^*u_j$ have convergent subsequences. Choose one subsequence for all $m$. The tail bound(75.20) makes their limits compatible and gives a vector $F\in\mathcal H^{\rm fr}$ for which $u_j-JF\to0$. In particular $J^*u_j\to F$ and $\|u_j\|\to\|F\|$. This argument retains chamber fluctuations, transverse functions and ground half-chamber data, rather than projecting them out of the hypothesis.

For every $h\in\mathcal H^{\rm fr}$ the positive form inequality is

$$
q_{0,\varepsilon}[u]+\|u\|^2
\ge2\operatorname{Re}\langle u,Jh\rangle
 -\langle Jh,(B_\varepsilon+1)^{-1}Jh\rangle.
\tag{75.21}
$$

It follows by completing the square against $(B_\varepsilon+1)^{-1}Jh$ in the form norm. Pass to the limit using(75.19). The supremum over $h$ on the right equals $q^{\rm fr}[F]+\|F\|^2$, with value $+\infty$ outside $\mathcal Q^{\rm fr}$. To see the equality directly, expand in the eigenbasis of $B$ and maximize each finite sum $2\operatorname{Re}\sum F_j\overline{h_j}-\sum|h_j|^2/(1+\lambda_j)$; its supremum is $\sum(1+\lambda_j)|F_j|^2$. Subtract the converging squared norms to obtain(75.18). Selecting a subsequence attaining the energy lower limit, if necessary, proves the stated inequality. At no step are the finite-thickness averages $J^*u_j$ assumed to satisfy the global effective matching conditions. $\square$

**Lemma 75.6 (every collision condition in the hard lower limit).** If the $u_j$ in75.5 are zero extensions of members of $\mathcal Q_{\varepsilon_j,R}^{\rm D}$ for(75.13), then their limit satisfies $F\in E\mathcal Q^{\rm hc}$. Hence

$$
a k_{\delta,2}[E^*F]\le\liminf_jq_{0,\varepsilon_j}[u_j].
\tag{75.22}
$$

**Proof.** For chamber coverage, $u_j=0$ on every entire source chamber pair, so $(J^*u_j)_{pp}=0$ exactly. For the strengthening, fix any $\kappa>0$ and set $h_p=\min\{\ell_p/2,\kappa/4\}>0$. The ball $A_p^\varepsilon=b_p^\varepsilon+h_pr_\varepsilon B_1$ lies in $Z_p^\varepsilon$, and $A_p^\varepsilon\times A_p^\varepsilon$ lies strictly in the forbidden region. Its fraction of the chamber-product volume is

$$
\theta_p=(\delta\omega_s h_p^s)^2>0,
\qquad
\int_{A_p^\varepsilon\times A_p^\varepsilon}|JF|^2
                         =\theta_p|F_{pp}|^2.
\tag{75.23}
$$

Since $u_j$ vanishes there, (75.18) implies $\theta_p|F_{pp}|^2\le\|u_j-JF\|^2\to0$. This forces every $F_{pp}=0$, even when part of a chamber pair remains allowed.

On one straight cylinder the transverse separation is at most $2\rho\varepsilon$, where $\rho=\omega_{s-1}^{-1/(s-1)}$. Since $R_\varepsilon/\varepsilon=\kappa\varepsilon^{-1/s}\to\infty$, for all sufficiently small $\varepsilon$ every transverse pair above $|x-y|<R_\varepsilon/2$ has physical separation less than $R_\varepsilon$. Consequently the averaged same-cable cell $f_\varepsilon=(J^*u_\varepsilon)_{ee}$ vanishes on this entire longitudinal strip. Transverse averaging of the restriction to the cylinder product commutes with its weak longitudinal derivatives. Cauchy–Schwarz, the fiber volumes and(75.8) give

$$
\delta^2\|f_\varepsilon\|_2^2\le\|u_\varepsilon\|^2,
\qquad a\delta\int_{(0,1)^2}|\nabla f_\varepsilon|^2
                                      \le q_{0,\varepsilon}[u_\varepsilon].
\tag{75.24}
$$

Thus these functions are bounded in $H^1$ on the full square. Their strong $L^2$ limit is $F_{ee}$, because $J^*u_j\to F$. A weak $H^1$ subsequence has that same limit. Each $f_\varepsilon$ has zero trace from both triangles on the diagonal, since it vanishes in a neighborhood of it; continuity of the triangle trace maps preserves these zero traces in the weak limit. Together with75.5 and all the free matching and grounding identities, (75.2) proves the exact hard-core domain assertion. In particular the shared-port slice endpoint conditions follow from $F_{pp}=0$ and the free endpoint equalities. No cell-corner point value is used. Equation(75.22) is then the free lower bound with its unchanged coefficients. $\square$

**Lemma 75.7 (a compatible form core avoiding the entire collision set).** In $E\mathcal Q^{\rm hc}$ the bounded members which vanish whenever $d_X(x,y)<h$ for some $h>0$ depending on the member are dense in the full form norm $\bigl(q^{\rm fr}[F]+\|F\|^2\bigr)^{1/2}$.

**Proof.** First apply the same scalar clipping to the real and imaginary parts on every stratum, including the atomic coordinates. The map fixes zero, commutes with exchange and with Sobolev traces, and therefore preserves every endpoint and boundary equality, the grounded zeros and the zero diagonal traces. As the clipping bound tends to infinity, the functions and weak derivatives converge in the finite weighted direct-sum form norm. This follows from the Sobolev chain rule: the derivative of a clipped real function is its original derivative on the unclipped set and zero on the clipped set, so the derivative difference tends to zero by dominated convergence. The imaginary part is identical. It suffices to treat a bounded $F\in E\mathcal Q^{\rm hc}$.

For $0<\eta<1/4$, define the single real multiplier on $X_D^2$

$$
\chi_\eta(t)=
\begin{cases}
0,&0\le t\le\eta^2,\\
\log(t/\eta^2)/\log(1/\eta),&\eta^2<t<\eta,\\
1,&t\ge\eta,
\end{cases}
\qquad F_\eta(x,y)=\chi_\eta(d_X(x,y))F(x,y).
\tag{75.25}
$$

On every interval and cell this is a Lipschitz multiplier for each fixed $\eta$. The metric $d_X$ is continuous under all the incidence identifications. Thus the cell multiplier at a port is precisely the corresponding slice multiplier, and its slice endpoint is the atomic multiplier. All matching equalities persist. Zero ground and collision traces persist, and the multiplier is exchange symmetric. Its value is one on distinct atomic pairs, whose graph distances are at least one; the diagonal atomic values remain zero.

The norm difference tends to zero by dominated convergence on all continuous strata. The derivative difference is the sum of $(\chi_\eta-1)\nabla F$, which also tends to zero by dominated convergence, and $F\nabla\chi_\eta$. Only three types of strata can meet the graph collision neighborhood of radius less than $1/4$.

On a mixed slice incident at its equal atomic port, the graph distance is the endpoint coordinate $t$, and that slice has zero endpoint there. For any $v\in H^1(0,L)$ with $v(0)=0$,

$$
\int_0^L\frac{|v(t)|^2}{t^2}\,dt
\le4\int_0^L|v'(t)|^2\,dt.
\tag{75.26}
$$

For smooth functions vanishing at zero, integration by parts gives an upper bound $2\operatorname{Re}\int v'\overline v/t$, the boundary term at $L$ being nonpositive. Cauchy–Schwarz gives(75.26), and $H^1$ approximation with the zero endpoint proves the general assertion. Since $|\chi_\eta'(t)|\le1/(t\log(1/\eta))$, the additional derivative energy on such a slice is bounded by its fixed Hardy integral times $\log(1/\eta)^{-2}$, and tends to zero.

On each same-cable triangle, $d_X(x,y)=|x-y|$. Apply(75.26) on almost every section $x>y$ starting at $x=y$ and ending at $x=1$, and on the sections $x<y$ with reversed coordinate. The section endpoint is the zero diagonal trace. More explicitly the affine coordinates $(t,y)=(x-y,y)$ flatten the diagonal; on each closed subinterval of $0<y<1$ they give a rectangular collar of that side. Fubini's $H^1$ section identity and continuity of the flat boundary trace identify the section endpoint with the triangle trace there. Exhausting $0<y<1$ proves the identity almost everywhere; no value at either diagonal corner is needed. It yields

$$
\int_{(0,1)^2}\frac{|F_{ee}(x,y)|^2}{|x-y|^2}\,dx\,dy
\le4\int_{(0,1)^2}|\partial_xF_{ee}(x,y)|^2\,dx\,dy.
\tag{75.27}
$$

The two components of the cutoff gradient give at most twice this Hardy bound times $\log(1/\eta)^{-2}$. Both diagonal sides are included.

Finally, on two distinct cables meeting at a port, use their distances $u,v$ from that port. Near the shared corner $d_X=u+v$. Boundedness of $F$, without a corner point value, gives

$$
\begin{aligned}
\int |F|^2|\nabla\chi_\eta(u+v)|^2\,du\,dv
&\le\frac{2\|F\|_\infty^2}{\log(1/\eta)^2}
       \int_{\eta^2<u+v<\eta}\frac{du\,dv}{(u+v)^2}\\
&=\frac{2\|F\|_\infty^2}{\log(1/\eta)}\longrightarrow0.
\end{aligned}
\tag{75.28}
$$

The equality uses $u,v\ge0$ and $\eta<1$: the cross-section at $u+v=t$ contributes $t\,dt$. Distinct atoms, a nonincident atom/cable slice and nonincident cable cells have graph separation at least one and are unaffected. These cases exhaust the finite unit-cable tree. Multiplying the estimates by the exact positive weights in(75.3) and summing proves $F_\eta\to F$ in the complete form norm. Clipping followed by a diagonal choice of $\eta$ proves the assertion for every form vector, with every mixed slice and rectangle retained. $\square$

**Lemma 75.8 (exact form lift and complete recovery in the actual hole).** For every $F\in\mathcal Q^{\rm fr}$,

$$
JF\in\mathcal Q_{{\rm mix},\varepsilon},\qquad
\|JF\|=\|F\|,\qquad q_{0,\varepsilon}[JF]=q^{\rm fr}[F].
\tag{75.29}
$$

For every $f\in\mathcal Q^{\rm hc}$ there are $v_\varepsilon\in\mathcal Q_{\varepsilon,R}^{\rm D}$ such that

$$
\|\iota_\varepsilon v_\varepsilon-L_\varepsilon f\|\longrightarrow0,
\qquad q_{0,\varepsilon}[\iota_\varepsilon v_\varepsilon]
                                  \longrightarrow a k_{\delta,2}[f].
\tag{75.30}
$$

**Proof.** On each product of chamber and cylinder pieces the lift(75.7) is $H^1$. Across a matching plate, a cell trace equals its slice, and a slice endpoint equals its atomic value, so the physical traces agree in the other coordinate's entire piece. At a ground half-chamber the lift is zero and the adjacent cable endpoint trace is zero. These identities also give the required zero traces on both grounded product faces. Piecewise $H^1$ gluing proves global membership: integration of the weak-derivative identity against an interior smooth test function on all pieces cancels the matched interface trace terms; interface rims have boundary measure zero. The resulting piecewise derivatives belong to $L^2$. No derivative transmission or $H^2$ regularity is needed.

For the norm, $c_\varepsilon^4$ times the chamber/chamber, chamber/cylinder and cylinder/cylinder fiber volumes gives exactly $1,\delta,\delta^2$. Chambers contribute no derivative. In a chamber/cylinder piece the derivative coefficient is

$$
\beta c_\varepsilon^4
       \frac{\varepsilon^{s-1}}\delta\,\varepsilon^{s-1}=a,
\qquad
\beta c_\varepsilon^4\varepsilon^{2(s-1)}=a\delta
\quad\text{on a cylinder/cylinder piece}.
\tag{75.31}
$$

Both coordinate derivatives and both mixed orders are counted. This proves(75.29) on the complete form domain, rather than only on tensor or atomic data. It is a form identity, compatible with72.11's failure of exact finite-thickness operator intertwining.

Let $j_D:X_D\to\mathbb R^s$ be the fixed injective skeleton embedding of72.3, including all distinct ground tips. Collapse a source chamber to its port, a ground half-chamber to its ground tip, and a cylinder to its own unit longitudinal coordinate; call this piecewise map $\pi_\varepsilon$. The actual assembly gives a fixed $C_D<\infty$ with

$$
|x-j_D(\pi_\varepsilon x)|\le C_Dr_\varepsilon
\quad\text{on all physical pieces, for small }\varepsilon.
\tag{75.32}
$$

Here is the required quantitative geometric reason. Centre distances are $1+h_v+h_w=1+O(r_\varepsilon)$; recursive placement on the finite source moves every source centre by $O_D(r_\varepsilon)$. The ground-centre formula(72.8) is smooth near its fixed strictly positive square root, so it has the same displacement bound. Directions therefore differ by $O_D(r_\varepsilon)$, plate offsets are $O(r_\varepsilon)$, chamber diameters are $O(r_\varepsilon)$ and transverse radii are $O(\varepsilon)=o(r_\varepsilon)$. Comparing each physical longitudinal segment with its fixed unit skeleton segment proves(75.32).

The compact embedded tree has the inverse modulus

$$
\omega_D(t)=\sup\{d_X(\xi,\zeta):\xi,\zeta\in X_D,
                             |j_D(\xi)-j_D(\zeta)|\le t\},
\qquad \omega_D(t)\longrightarrow0\quad(t\downarrow0).
\tag{75.33}
$$

The last assertion follows from compactness and injectivity: a sequence violating it would have limiting distinct points with the same embedded position. Thus a forbidden physical pair obeys

$$
|x-y|\le R_\varepsilon
\quad\Longrightarrow\quad
d_X(\pi_\varepsilon x,\pi_\varepsilon y)
 \le\omega_D(R_\varepsilon+2C_Dr_\varepsilon)\longrightarrow0.
\tag{75.34}
$$

Fix any member of the core of75.7, vanishing for $d_X<h$. Its lift is zero on the whole physical forbidden set for all sufficiently small $\varepsilon$, by(75.34). Pieces with a ground half-chamber already have zero lift. Consequently its restriction to $G_{\varepsilon,R}$ belongs to exactly(75.9).

For arbitrary $f\in\mathcal Q^{\rm hc}$ choose core members $F_m\to Ef$ in the full form norm. For each $m$ choose a positive threshold below which $JF_m$ avoids the hole, and replace these thresholds by a decreasing sequence tending to zero. Let $m(\varepsilon)\to\infty$ increase sufficiently slowly that $JF_{m(\varepsilon)}$ avoids the hole. Set $v_\varepsilon=\iota_\varepsilon^*JF_{m(\varepsilon)}$. Its zero extension equals that lift. Equation(75.29) proves both limits in(75.30). The same source, geometry, radius and operators serve all inputs; only the recovery vector depends on $f$. This is mathematical form recovery, not an acquired preparation operation. $\square$

**Lemma 75.9 (the full original potentials and complete form convergence).** For each of the three prescriptions, every bounded shifted-energy hard sequence has a strongly identified subsequence whose limit lies in $\mathcal Q^{\rm hc}$ and satisfies the target form lower bound. Every member of $\mathcal Q^{\rm hc}$ has recovery for the entire corresponding form, with its original one-body field and complete pair coefficients.

**Proof.** Extend $U_\diamond$ to $\mathcal H^{\rm fr}$ by keeping the additive one-body value $-2g\phi(p)$ at $(p,p)$ and putting no pair term there. Denote this bounded multiplier by $\widehat U_\diamond$, and put $\widehat U_0=0$. Then direct comparison on every product piece in(75.7) gives the exact Hilbert-space identities

$$
W_{\varepsilon,C}J=J\widehat U_C,\qquad
\widehat U_CE=EU_C,\qquad
W_{\varepsilon,C}L_\varepsilon=L_\varepsilon U_C.
\tag{75.35}
$$

On a mixed stratum this identity retains the one atomic one-body value; on cells both one-body values and the pair term are zero. On a distinct atomic pair it retains both one-body values and exactly that pair coefficient. On a double atom the free extension has its specified additive value, which is immaterial after $E$. On ground half-chamber pieces the lift is zero. These cases verify the identity on all Hilbert data, without assuming that multiplication preserves form trace equalities.

If $u_\varepsilon-JF\to0$ in physical norm and the norms are bounded, boundedness of $W$ and(75.35) imply

$$
\langle u_\varepsilon,W_{\varepsilon,C}u_\varepsilon\rangle
 \longrightarrow\langle F,\widehat U_CF\rangle.
\tag{75.36}
$$

For example the absolute difference from the quadratic term of $JF$ is at most $M\|u_\varepsilon-JF\|(\|u_\varepsilon\|+\|F\|)$, and the term of $JF$ equals the target extension exactly. Set $b=M+1$. Both the physical and target shifted forms obey

$$
\begin{aligned}
h_{\varepsilon,C}[v]+b\|v\|^2
 &\ge q_{0,\varepsilon}[\iota_\varepsilon v]+\|v\|^2,\\
q_C[f]+b\|f\|^2&\ge a k_{\delta,2}[f]+\|f\|^2,
\qquad q_C=a k_{\delta,2}+\langle\,\cdot,U_C\,\cdot\rangle.
\end{aligned}
\tag{75.37}
$$

Thus a bounded shifted-energy sequence has the free compactness of75.5, the exact hard lower domain of75.6 and, by(75.36), the complete lower bound $q_C[f]\le\liminf h_{\varepsilon,C}[v_\varepsilon]$ whenever $\iota_\varepsilon v_\varepsilon-L_\varepsilon f\to0$. If the energy lower limit is finite, select a subsequence attaining it and apply those lemmas; if it is infinite the inequality is automatic. The recovery of75.8 and(75.36) give $h_{\varepsilon,C}[v_\varepsilon]\to q_C[f]$ for every $f\in\mathcal Q^{\rm hc}$. These are the lower and recovery assertions on the entire target domain for each actual law, with no restricted test class. $\square$

**Proposition 75.10 (arbitrary forcing and full operator norm).** The complete form assertions in75.9 imply both conclusions of75.4, uniformly on each fixed nonreal compact spectral set.

**Proof.** First use the common shift $b=M+1$. For an arbitrary sequence of forcings $f_\varepsilon\in\mathcal P_\varepsilon$ with $\|f_\varepsilon\|\le1$, let

$$
u_\varepsilon=\iota_\varepsilon(H_{\varepsilon,R,C}^{\rm D}+b)^{-1}
                                      \iota_\varepsilon^*f_\varepsilon.
\tag{75.38}
$$

The variational identity and(75.37) give $q_{0,\varepsilon}[u_\varepsilon]+\|u_\varepsilon\|^2\le1$: if $A$ is its shifted energy, then $A\le\|u_\varepsilon\|\le\sqrt A$. Extract a subsequence with $J^*f_\varepsilon\rightharpoonup h$ in the fixed $\mathcal H^{\rm fr}$ and $u_\varepsilon-L_\varepsilon u\to0$ with $u\in\mathcal Q^{\rm hc}$. Lemmas75.5–75.6 provide the latter conclusion, with no restriction on forcing.

The vector(75.38) minimizes, on the zero-extended allowed form domain, the strictly positive functional

$$
\mathcal F_\varepsilon(v)
 =h_{\varepsilon,C}[\iota_\varepsilon^*v]+b\|v\|^2
                     -2\operatorname{Re}\langle f_\varepsilon,v\rangle.
\tag{75.39}
$$

Its limiting functional is $\mathcal F(w)=q_C[w]+b\|w\|^2-2\operatorname{Re}\langle E^*h,w\rangle$. The lower bound of75.9 gives $\mathcal F(u)\le\liminf\mathcal F_\varepsilon(u_\varepsilon)$. For every $w\in\mathcal Q^{\rm hc}$ its complete recovery gives $\mathcal F_\varepsilon(v_\varepsilon)\to\mathcal F(w)$, including the forcing term. Indeed any strongly identified $v_\varepsilon=L_\varepsilon w+o(1)$ satisfies $\langle f_\varepsilon,v_\varepsilon\rangle\to\langle h,Ew\rangle$. Minimization therefore gives $\mathcal F(u)\le\mathcal F(w)$ for every $w$. The unique minimizer is

$$
u=(C+b)^{-1}E^*h.
\tag{75.40}
$$

The target resolvent is compact. Its shifted form norm is equivalent to the inherited free form norm on $E\mathcal Q^{\rm hc}$, by boundedness of $U_C$; the free form embedding is compact. Thus $(C+b)^{-1}E^*J^*f_\varepsilon\to u$ strongly. Since $L_\varepsilon$ is an isometry, the difference between(75.38) and $L_\varepsilon(C+b)^{-1}L_\varepsilon^*f_\varepsilon$ tends to zero along this subsequence. If the corresponding operator norm had a positive upper limit, a sequence of unit forcings realizing at least half that discrepancy would have a subsequence just shown to have vanishing discrepancy. This contradiction proves

$$
\|S_\varepsilon-T_\varepsilon^0\|\longrightarrow0,\qquad
S_\varepsilon=\iota_\varepsilon(H_{\varepsilon,R,C}^{\rm D}+b)^{-1}
                      \iota_\varepsilon^*,\quad
T_\varepsilon^0=L_\varepsilon(C+b)^{-1}L_\varepsilon^*.
\tag{75.41}
$$

Both operators are bounded nonnegative operators on the full $\mathcal P_\varepsilon$, with spectra in $[0,1]$. For nonreal $z$ put $c=z+b$ and $h_z(t)=t/(1-ct)$. Its value at zero is zero. Because $\iota_\varepsilon$ and $L_\varepsilon$ are isometries on their respective original carriers, spectral calculus gives

$$
\begin{aligned}
h_z(S_\varepsilon)
 &=\iota_\varepsilon(H_{\varepsilon,R,C}^{\rm D}-z)^{-1}
                                                   \iota_\varepsilon^*,\\
h_z(T_\varepsilon^0)&=K_{\varepsilon,C}(z).
\end{aligned}
\tag{75.42}
$$

This correctly preserves zero action on the two possibly different orthogonal complements. For a fixed nonempty compact $K\subset\mathbb C\setminus\mathbb R$,

$$
d_K=\min_{z\in K,\ 0\le t\le1}|1-(z+b)t|>0.
\tag{75.43}
$$

The expression cannot vanish: at $t=0$ it is one, and at $t>0$ vanishing would force $z$ real. Compactness supplies the positive minimum. The elementary bounded-operator identity

$$
h_z(S)-h_z(T)
 =(I-cS)^{-1}(S-T)(I-cT)^{-1}
\tag{75.44}
$$

holds by multiplying on the left by $I-cS$ and on the right by $I-cT$: the middle expression becomes $S(I-cT)-(I-cS)T=S-T$, without assuming that $S$ and $T$ commute. It bounds the supremum of(75.14)'s full discrepancies by $d_K^{-2}\|S_\varepsilon-T_\varepsilon^0\|$. This proves full norm convergence uniformly on $K$. Compressing the full difference by $\iota_\varepsilon^*$ and $\iota_\varepsilon$ gives exactly the allowed-carrier difference, hence

$$
D_{\varepsilon,C}^{\rm a}(z)\le D_{\varepsilon,C}^0(z).
\tag{75.45}
$$

No isometry of the restricted target lift was used. The three prescriptions are finite in number and share all geometry and radius choices, so taking their maximum preserves convergence and gives the common tolerance threshold in75.4. $\square$

**Proposition 75.11 (retained complements, both cross blocks and restriction loss).** Let $\mathsf S_{\varepsilon,C}(z)=\iota_\varepsilon(H_{\varepsilon,R,C}^{\rm D}-z)^{-1}\iota_\varepsilon^*$, and put

$$
P_\varepsilon=L_\varepsilon L_\varepsilon^*,\quad
Q_\varepsilon=I-P_\varepsilon,\quad
A_\varepsilon=\iota_\varepsilon\iota_\varepsilon^*,\quad
F_\varepsilon^{\rm forb}=I-A_\varepsilon.
\tag{75.46}
$$

The entire $Q_\varepsilon$ block and both cross blocks of the actual extended resolvent tend to zero uniformly on $K$:

$$
\begin{aligned}
\|Q_\varepsilon\mathsf S_{\varepsilon,C}(z)Q_\varepsilon\|,
\quad\|Q_\varepsilon\mathsf S_{\varepsilon,C}(z)P_\varepsilon\|,
\quad\|P_\varepsilon\mathsf S_{\varepsilon,C}(z)Q_\varepsilon\|
&\le D_{\varepsilon,C}^0(z),\\
\|K_{\varepsilon,C}(z)F_\varepsilon^{\rm forb}\|,
\quad\|F_\varepsilon^{\rm forb}K_{\varepsilon,C}(z)\|
&\le D_{\varepsilon,C}^0(z).
\end{aligned}
\tag{75.47}
$$

Nevertheless, for all sufficiently small $\varepsilon$, the raw restricted lift satisfies

$$
\|I-T_\varepsilon^*T_\varepsilon\|_{\mathcal B(\mathcal K)}=1.
\tag{75.48}
$$

**Proof.** The target resolvent has only a $P_\varepsilon$–$P_\varepsilon$ block. Multiplying the full difference in(75.14) by these orthogonal projections proves the first three bounds. The actual extended resolvent vanishes on the forbidden subspace in both directions, proving the last two. Thus the estimates include nonconstant chamber and transverse functions, ground half-chamber functions, the excluded effective atomic coordinates, arbitrary complementary forcing and both directions of coupling to the retained range.

For(75.48), choose any cable. A nonzero symmetric smooth cell function supported in $[1/4,3/4]^2\cap\{|x-y|<R_\varepsilon/4\}$, with every other stratum zero, defines a target Hilbert vector; normalize it in the actual $\delta^2$ cell norm. Choose an even factor vanishing at $x=y$, so the vector also belongs to the literal target form domain, with all outer cell traces zero. Since $R_\varepsilon/\varepsilon\to\infty$, its entire physical transverse product lies in the forbidden region for small $\varepsilon$, by the same separation estimate as75.6. Its restriction $T_\varepsilon f$ is zero. The positive contraction $T_\varepsilon^*T_\varepsilon$ therefore has a unit kernel vector, while $0\le I-T_\varepsilon^*T_\varepsilon\le I$, proving(75.48). For these normalized vectors, (75.27) and their strip support give $a k_{\delta,2}[f]\ge4a/(\delta R_\varepsilon^2)\to\infty$. This explains why exact raw isometry cannot replace the complete lower, recovery and compact resolvent proof. The allowed comparison(75.15) remains an operator norm on its entire actual carrier. $\square$

**Corollary 75.12 (the mesoscopic alternative and the necessary-range account).** The same full target theorem, exact multipliers, maps and both hard-carrier comparisons hold if(75.13) is replaced by

$$
R_\varepsilon\longrightarrow0,\qquad
R_\varepsilon/r_\varepsilon\longrightarrow\infty.
\tag{75.49}
$$

For the fixed chamber radius of75.4 the necessary hard-range quotient of74 is

$$
\frac{R_\varepsilon^{s-2}}{\varepsilon^{s-1}}
 =\kappa^{s-2}r_\varepsilon^{-2}\longrightarrow\infty.
\tag{75.50}
$$

**Proof.** Under(75.49) every chamber pair is eventually fully covered by(75.16), and $R_\varepsilon/\varepsilon\to\infty$ gives the full same-cylinder forbidden strip. The core and exact form lift are unchanged; recovery uses $\omega_D(R_\varepsilon+2C_Dr_\varepsilon)\to0$, which still holds. Thus75.5–75.10 apply verbatim to these stated inequalities, proving the whole conclusion. Equation(75.50) follows from $r_\varepsilon^s=\varepsilon^{s-1}$. It is compatible with74.8's necessary range condition. Its divergence alone is not used as a sufficient criterion for arbitrary interactions of74.2. The selected radius has $R_\varepsilon/\varepsilon\to\infty$ and therefore lies outside that chapter's separate microscopic assumption $h_\varepsilon=o(\varepsilon)$. The mesoscopic route requires a larger asymptotic range than75.4 and supplies the same stated target conclusion; these mathematical statements give no physical cost ordering between installations. $\square$

**Theorem 75.13 (a finite-height alternative on the full carrier).** Keep exactly75.1–75.3's source, geometry and step multipliers, but replace the hard domain by the entire mixed-ground domain. Fix any $\kappa>0$, use $R_\varepsilon=\kappa r_\varepsilon$, and choose finite heights $\Lambda_\varepsilon\ge0$ with

$$
\Lambda_\varepsilon R_\varepsilon\longrightarrow\infty.
\tag{75.51}
$$

Let $H_{\varepsilon,C}^{\Lambda}$ be the densely defined full-product operator of the closed form

$$
q_{\varepsilon,C}^{\Lambda}[u]
 =q_{0,\varepsilon}[u]
 +\Lambda_\varepsilon\int_{|x-y|\le R_\varepsilon}|u|^2
 +\langle u,W_{\varepsilon,C}u\rangle,
\qquad u\in\mathcal Q_{{\rm mix},\varepsilon}.
\tag{75.52}
$$

For every fixed compact $K\subset\mathbb C\setminus\mathbb R$,

$$
\max_{C\in\{C_0,C_{\rm c},C_{\rm k}\}}\ \sup_{z\in K}
\big\|(H_{\varepsilon,C}^{\Lambda}-z)^{-1}-K_{\varepsilon,C}(z)\big\|
                         _{\mathcal B(\mathcal P_\varepsilon)}\longrightarrow0.
\tag{75.53}
$$

This is a sufficient height schedule on the full unchanged target, not a sharp height threshold or a physical price assertion.

**Proof.** Each finite height is a bounded nonnegative perturbation for its individual $\varepsilon$, so the form is closed and dense on the full carrier, with lower bound $-M$. A bounded shifted-energy sequence satisfies both the free bound(75.17) and

$$
\Lambda_\varepsilon\int_{|x-y|\le R_\varepsilon}|u_\varepsilon|^2\le A
\tag{75.54}
$$

for a fixed $A$. Obtain $u_\varepsilon-JF\to0$ and $F\in\mathcal Q^{\rm fr}$ from75.5. Since $R_\varepsilon\to0$, (75.51) implies $\Lambda_\varepsilon\to\infty$. On the positive-fraction ball products of(75.23),

$$
\theta_p|F_{pp}|^2
\le2\|u_\varepsilon-JF\|^2
       +2\int_{|x-y|\le R_\varepsilon}|u_\varepsilon|^2\longrightarrow0.
\tag{75.55}
$$

Thus the atomic collisions vanish for every fixed positive $\kappa$.

For a same-cable average $f_\varepsilon=(J^*u_\varepsilon)_{ee}$, (75.24) still holds. The complete transverse strip is inside the physical penalty region, so Jensen gives

$$
\delta^2\int_{|x-y|<R_\varepsilon/2}|f_\varepsilon(x,y)|^2\,dx\,dy
                                  \le A/\Lambda_\varepsilon.
\tag{75.56}
$$

For every $f\in H^1((0,1)^2)$ and $0<h<1/2$ the diagonal trace satisfies

$$
\|\operatorname{Tr}_{x=y}f\|_{L^2(0,1)}^2
\le \frac{2}{h}\int_{|x-y|<h}|f(x,y)|^2\,dx\,dy
       +2h\int_{(0,1)^2}|\partial_xf|^2\,dx\,dy.
\tag{75.57}
$$

Indeed for $y\le1/2$ use the section $v(t)=f(y+t,y)$, $0<t<h$, and for $y>1/2$ use $v(t)=f(y-t,y)$. The fundamental theorem and Cauchy–Schwarz give $|v(0)|^2\le2|v(t)|^2+2t\int_0^t|v'|^2$. Average in $t$, then integrate in $y$; both section regions are in the indicated strip and their union has no multiplicity. Smooth approximation and continuity of the diagonal trace prove the general $H^1$ assertion.

Apply(75.57) with $h=R_\varepsilon/2$. Equations(75.24), (75.56) and(75.51) show that these diagonal traces tend to zero. The strong $L^2$ and weak $H^1$ limit is $F_{ee}$, so it has zero diagonal trace. Now(75.2) gives exactly the full hard-core target domain, including all shared-port and ground conditions. The free lower bound, the nonnegative penalty and(75.36) give the complete target lower bound.

For every target form vector use precisely75.8's collision-avoiding recovery. Its lift vanishes in the physical penalty region for sufficiently small $\varepsilon$ at each fixed core stage, so its penalty is exactly zero, regardless of the height. The same slow diagonal choice supplies complete form recovery. These two form directions and the free compactness allow the arbitrary-forcing minimization proof of75.10 with(75.52) in place of the hard form and with identity inclusion on the full carrier. The shifted energy still bounds the entire free energy; its recovery still attains the target functional for every competitor. Compactness and(75.44) therefore prove(75.53), including the same complement and both cross blocks relative to $P_\varepsilon$. The finite-height route adds the diverging height coordinate(75.51), whereas the hard route declares an ideal Dirichlet installation. No price model equating or ordering those controls is assumed. $\square$

**Corollary 75.14 (the unchanged one-particle field on the same assembly).** On the one-particle physical carrier of72.10, the installed multiplier $-g\Phi_\varepsilon$ yields the original complete one-particle operator $\mathcal T^\diamond_{\delta,D,1}=A_{\delta,D,1}-g\phi_A$, identically for both prescriptions, in full norm-resolvent comparison on every fixed nonreal compact set.

**Proof.** This is a bounded-perturbation consumer of72.10, with its exact $J_\varepsilon$ and adjoint(72.30). The same piecewise formulas give $(-g\Phi_\varepsilon)J_\varepsilon=J_\varepsilon(-g\phi_A)$ and both potential norms are at most $g$. Choose $b_1>g$. The free shifted resolvents converge in norm by72.10 and continuous resolvent calculus for nonnegative operators. Expand the perturbed resolvents in their Neumann series at $-b_1$. The $n$th terms are products of $n+1$ free resolvents and $n$ potential factors; covariance gives exactly the lifted target series. If the free discrepancy is $\eta_\varepsilon$, telescoping products bound the difference of the $n$th terms by $(n+1)(g/b_1)^n\eta_\varepsilon$. Summation gives an upper bound $(1-g/b_1)^{-2}\eta_\varepsilon\to0$. The identity(75.44), on the bounded interval containing these positive shifted spectra, transfers it uniformly to every fixed nonreal compact set. This neither changes the one-body field under killing nor re-proves the accepted free one-particle supplier. $\square$

**Definition 75.15 (source coefficients, mature reuse and precise mathematical scope).** On the five-port witness $(o,L,R,LL,LR)$, (75.5) retains all ten source coefficients:

$$
\begin{array}{c|cccccccccc}
\{p,q\}&oL&oR&oLL&oLR&LR&L\,LL&L\,LR&R\,LL&R\,LR&LL\,LR\\ \hline
G_D^{\rm c}&1/2&1/2&1/4&1/4&1/4&3/8&3/8&1/8&1/8&3/16\\
G_D^{\rm k}&9/26&7/26&3/26&3/26&3/26&5/26&5/26&1/26&1/26&5/78
\end{array}
$$

This is the original64.1 witness, not the definition of either law for general $D$. Equations(75.5) and(75.11) use the entire corresponding source kernel. The three comparisons share the original source, all geometry, one radius family, maps, kinetic coefficients and grounding. The two unequal complete pair prescriptions are separate operators; the theorem does not provide a single physical generator equal to both or a free acquired switch between them.

The accepted ordinary suppliers are precisely72's separated exact-length geometry and full free one-particle correspondence,73's complete free product limit and domain equality(73.8), and74's hard carriers, form typing and necessary obstructions. Their source is the [second continuation at its immutable Chapter74 pin](https://github.com/the-omega-institute/trureturing/blob/1e4a194133891dadad9fbdefb4b590eefa49b9cc/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_II.md). The original measure, domain, fields, pair kernels and material boundaries are64.5,62.2–62.4,63.13,66.10,67.11 and68.7 in the [first continuation at its immutable pin](https://github.com/the-omega-institute/trureturing/blob/0916822f1ee0d1f84783170ca062227d9ba9c253/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md). These are scoped ordinary premises; their source publication is not a new kernel or physical verification.

The mature thinning theorem used through72 is Cherednichenko–Ershova–Kiselev, [*Norm-resolvent convergence for Neumann Laplacians on manifolds thinning to graphs*, arXiv:2205.04397v4](https://arxiv.org/html/2205.04397v4), Section2, Section3 and Theorem4.5 with equations(16)–(18). Its straight cylinders, resonant chamber volumes, contact geometry, all-Neumann double and massive-vertex operator are matched in72 before its odd grounding restriction. Chapter75 does not import an interacting conclusion from that donor. Its new bridge is the explicit lower domain, compatible all-stratum core, actual physical recovery and arbitrary-forcing norm proof above.

Seiringer–Yin, [*The Lieb–Liniger Model as a Limit of Dilute Bosons in Three Dimensions*, arXiv:0709.4022v1](https://arxiv.org/abs/0709.4022v1), treats fixed particle number and longitudinal scale, separable confining traps and scattering-length-normalized nonnegative interactions, including hard spheres, under its stated transverse and scattering separation. Its effective coupling may tend to infinity, and its norm-resolvent comparison subtracts transverse energy and uses the transverse ground-state projection. That different carrier supplies neither the massive source atoms, their mixed traces, nor either complete kernel here. No trap error estimate or interacting donor theorem is transferred. The Hardy, cutoff, averaging, variational and resolvent identities needed for this bridge are proved in this chapter.

The [same-carrier observer normalization](https://github.com/the-omega-institute/trureturing/blob/aaaf5bb64e78f915a42ccbba033df7a376979502/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.md), particularly1.6 and1.14–1.15, is source-attributed evidence about a complete nominal observer carrier and its stated execution/address fee. The [promised-risk acquisition result](https://github.com/the-omega-institute/trureturing/blob/aaaf5bb64e78f915a42ccbba033df7a376979502/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROMISED_RISK_HISTORY_LOCALIZATION.md),7.3 and8.1–8.2, distinguishes non-effective acquired-history localization across COMPLETE budgets from fixed-tuple finite existence and a separately scoped coarse certificate. Those different carriers and charges supply no continuum non-effectivity theorem or radius schedule here. In particular the qualitative $\varepsilon_0$ of75.4 is not asserted to be an effective acquired finite-execution certificate.

No rate, sharp exclusion or height threshold, minimum radius, physical control optimum or total-resource optimum is asserted. The fixed-positive-$\kappa$ strengthening uses the uniform interior balls of the supplied chambers; it is not a theorem for arbitrary degenerate chamber families or for $\kappa=\kappa_\varepsilon\to0$. Fixed $D$, positive fixed $\delta$, commissioned positive $a$, fixed reference geometry and fixed $s$ are material quantifiers. All fixed $s\ge3$ are in scope. There is no growing-source, varying-density, dimension-uniform or growing-spectral-window assertion, nor an operator-norm finite-clock evolution assertion.

**Definition 75.16 (retained native, field, acquisition and lifetime obligations).** The sufficient particle correspondence of75.4 reduces the full-domain realization gap left open after73 and the merely necessary range/strength account of74. It leaves the original sustained source/native/full-field/acquisition/resource/why-three programme active, with the following material obligations unchanged.

Every literal $\alpha/\beta$ label and bracket, left/right order and distinct occurrence remains; so do immutable INITIAL, one original fixed cap, source-independent initialization, actual versions and contexts, complete candidates and original guards, every acceptance and refusal, destructive operations, original numerical Read, absorbing Stop and actually acquired chronological records. The original actor's arbitrary, unbounded or possibly zero $a$, untagged radius-$7/25$ $b$ and joint adversarial or history-dependent errors remain distinct from the positive commissioned parameters in75.1. Whole-rho operations, beta-empty accepted label changes and the distinct Left/Right grafts retain their actual root, degree, field and domain/dynamic covariance duties. A whole-rho supplier does not grant either graft law. No candidate Read after refusal or service after Stop is introduced by a fixed-source resolvent.

The complete fixed-cap field bank, all $2^H-1$ oscillator modes, their excitations, unused spectators and auxiliary factors remain, as do every unknown particle/field/auxiliary correlation, the full joint norm, common reference and actual clock. The balanced coordinate/momentum field and complete source inverse of67 retain their on-site self-energy compensation, field-number/moment ingress hypotheses and atom-only displacement/domain boundary. The ordinary particle theorem proves no coupled-field generator comparison and certifies no unknown auxiliary ingress. Actual source-qualified local and isotropic mediation, stiffness/compensation installation, genuine switching, unknown-state ingress and recovery, retained-operation and metric correspondence, Read/Stop covariance and accepted-graft retained-carrier laws still need their own proofs. Particle form recovery is not native state recovery or preparation. There is no hidden trace, vacuum restriction, reset, cloning, independent resampling or calibrated-state re-preparation.

The common $\Pi$ of63.13 keeps its full-vector and spanning assumptions, common zero, whole quadratic-distance/positive-semidefinite Gram relation, at least two independent directions, alternating bilinear exact-area/Jacobi law, actual orthonormal probes, finite binary calibration and hidden-kernel-preserving generator conditions. Neither chamber averaging nor an abstract Hilbert-space identification supplies them, a field port or a clock.

The three acquisition contracts remain separate. The immutable composition-promised endpoint contract of57 retains fixed depth caps, common source-independent initialization, each actual query/reply history, correct finite stopping on every promised positive and negative source and distinct actual-address fees; it supplies no old-source archive. The paid positive-root archive/exact nonadvancing-cut contract retains its exact port, finite stopping and decoding, protected written records after refusal or closure, aligned actual generation, trusted markers, absence of unrecorded source change, closed strong ports and paid write/protect/retain/query rights. All reply-affecting retained source influence belongs in that service price. The phase-coherent full-tail contract retains its own once-sampled-depth actual Read process and paid stopped transcript. None grants copied source, reset, resampling, unknown-state preparation or an exact-limit Read, and none of their state counts, radii, update matrices or clocks is silently transported to this particle theorem.

Actual reference preparation and calibration, finite clock conversion, full error handling and usable finite execution/precision certificates remain unsupplied here. Every construction, acquisition, preparation, field/compensation/stiffness installation, exclusion or repulsion control, switching, source service, production, storage, hold, retention, maintenance and precision charge, including service durations and total lifetime price, remains a priced obligation. The installation of exact $W$, the ideal Dirichlet constraint or the diverging finite-height schedule is an explicit model hypothesis, not a free apparatus capability. Volume ratios, stratum counts, normalized measures and infinite-dimensional interval/cell spaces are not finite digital memory, physical masses or measured cost advantages.

For spatial realization, the original operation/metric bridge, packing, transverse, exterior, leakage and collision controls remain. The planar prescribed-length problem of72.13 still requires every centre distance $1+h_v+h_w$, both distinct grounded stubs ending on one grounding line, and crossing-free clearance with port margins. The existence of the supplied assembly separately in every fixed $s\ge3$ selects no unique three-dimensional ambient space. The ordinary result neither establishes global physical impossibility in another dimension nor settles an actual clock or lifetime price. These boundaries retain the full original goal rather than treating one fixed-source sufficient theorem as its completion.

## 75.99 追加锚（本行以下为增补区）

## 76. Planar grounding width and the minimum universal dimension of the unit skeleton

**Definition 76.1 (the commissioned template and its quantifiers).** Retain an
authentic nonempty finite ordered full binary source $D$ from
Definitions55.1,60.1,66.1 and67.1 of the
[first continuation](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md).
Every label, bracket, left/right address and distinct occurrence remains part
of the source. Write $o$ for its current root and put

$$
\ell(D)=\#\operatorname{Leaf}(D),\qquad
h(D)=\max_{p\in D}|p|.
\tag{76.1}
$$

Here $|p|$ counts inherited source seams from the current root; ground stubs
do not contribute to $h(D)$. The skeleton has precisely those seams and two
distinct stubs at **every** current leaf. Its total incidence is two at the
root and three at every nonroot source vertex; each ground tip has incidence
one. There are no further edges or identifications.

For an integer $s\ge1$, let $E_s(D)$ mean an injective placement of all source
vertices and ground tips in $\mathbb R^{s-1}\times\mathbb R$, with height
coordinate $y$, satisfying the following complete spatial contract. Every
source vertex has $1/4<y_p<3/4$. Every inherited seam and each of the two
stubs at every leaf is a straight Euclidean segment of length exactly one.
All ground tips are globally distinct and lie in the height-zero hyperplane
$\{y=0\}$. Segments intersect only at the images of their prescribed common
graph endpoints, and no vertex lies on a nonincident segment. The placement
has positive minimum incident-ray angle and positive clearance between
nonincident compact segments and vertices, with margins allowed to depend
on this finite source and placement. Thus the ground locus is a line for
$s=2$ and a plane for $s=3$.

These are precisely the straight skeleton conditions of Proposition72.3,
with its finite separation margins. The height band is commissioned spatial
data, not a consequence of literal substitution or a native necessity.
Universality means a separate placement for each authentic finite current
source at its separately legal, predeclared fixed cap. It supplies neither
one apparatus for all sources and histories nor a source- or cap-uniform
clearance or angle bound. The new assertion is finite exact geometry; it
has no thinning parameter, spectral limit, clock or precision regime.

**Theorem 76.2 (all-leaf planar separation and strict width necessity).**
For every $D$ of76.1 and every placement satisfying $E_2(D)$, put

$$
b_p=\sqrt{1-y_p^2},\qquad
I_p=[x_p-b_p,x_p+b_p],\qquad p\in\operatorname{Leaf}(D).
\tag{76.2}
$$

The closed grounding intervals $I_p$ are pairwise disjoint. If $W$ is the
horizontal span of all ground tips, then

$$
\ell(D)\frac{\sqrt7}{2}
 <\sum_{p\in\operatorname{Leaf}(D)}|I_p|
 \le W<2h(D)+2.
\tag{76.3}
$$

In particular the strict necessary inequality is
$\ell(D)\sqrt7/2<2h(D)+2$, and hence also the non-strict bound in the
original planar question. The proof needs no additional planar angle or
clearance hypothesis beyond the stated incidence and nonintersection.

**Proof.** A unit segment from $p=(x_p,y_p)$ to $(X,0)$ must satisfy
$(X-x_p)^2+y_p^2=1$. Since $0<y_p<1$, there are exactly two possible tips,
$g_p^-=(x_p-b_p,0)$ and $g_p^+=(x_p+b_p,0)$. Distinctness forces the two
actual stubs to use both. Write

$$
V_p=[g_p^-,p]\cup[p,g_p^+],\qquad
\Delta_p=\operatorname{conv}\{g_p^-,p,g_p^+\},\qquad
F_p(X,Y)=\frac{|X-x_p|}{b_p}+\frac{Y}{y_p}-1.
\tag{76.4}
$$

In $Y>0$, $F_p=0$ is exactly $V_p$ with its ground tips removed,
and $F_p<0$ is the triangle interior. The base $I_p\times\{0\}$ closes
the triangle only for this proof; it is no installed graph edge or cable.

Suppose $D$ is not a singleton, and let $v$ be the source parent of a leaf
$p$. Every $z\in\Delta_p$ of positive height has a convex representation
$z=\theta p+\mu g_p^-+\eta g_p^+$, where the coefficients are nonnegative,
sum to one, and $\theta=Y(z)/y_p>0$. Therefore

$$
|z-p|\le\mu|g_p^--p|+\eta|g_p^+-p|
       =\mu+\eta=1-\theta<1.
\tag{76.5}
$$

But $|v-p|=1$ and $Y(v)>0$, so $v\notin\Delta_p$ and $F_p(v)>0$.
Delete $p$ and its parent seam from the ungrounded source tree as a
mathematical proof device. The remaining source tree is connected and
contains $v$ and every other leaf. Its straight segments stay at positive
height. It avoids $V_p$, since it has no graph endpoint in common with
either stub of $p$. Consequently $F_p$ never vanishes on that connected
remainder. Continuity along its paths and $F_p(v)>0$ imply $F_p>0$
throughout it, including at every other leaf $q$.

If a ground tip $g=(X,0)$ of $q$ lay in the interior of $I_p$, then
$F_p(g)<0$. On the actual stub from $q$ to $g$, the intermediate value
theorem would give $F_p=0$ before reaching the ground. That point has
positive height and belongs to $V_p$, contradicting literal
nonintersection. A tip of $q$ cannot equal an endpoint of $I_p$ either,
because all tips are globally distinct. Thus no other leaf's ground tip
belongs to $I_p$. Apply the same argument with each leaf as $p$. Two
closed intervals with four distinct endpoints can overlap only if an
endpoint of one lies in the other's interior, also in the nested case.
This proves pairwise disjointness. For a singleton there is only one
interval, so the separation assertion is immediate. Leaf deletion above
is not a source operation and changes no source or producer carrier.

For every leaf, $y_p<3/4$ gives
$|I_p|=2\sqrt{1-y_p^2}>\sqrt7/2$. A root-to-leaf path has at most
$h(D)$ unit seams, whence $|x_p-x_o|\le h(D)$. Each tip differs
horizontally from its leaf by $b_p<1$. All finitely many tips therefore
lie strictly between $x_o-h(D)-1$ and $x_o+h(D)+1$, giving
$W<2h(D)+2$. Disjoint intervals have total length at most their enclosing
span $W$. Summing their strict width floors proves76.3, including the
singleton case. $\square$

**Proposition 76.3 (a literal obstruction at one separately fixed cap).**
Use the substitution family $T_n=\rho^n(\alpha)$ and its existing ordered
Fibonacci recurrence, supplied by55.1:

$$
T_0=\alpha,\qquad T_1=\beta,\qquad
T_{n+2}=\langle T_{n+1},T_n\rangle.
\tag{76.6}
$$

Here $T_n$ denotes this family only, not65.1's balanced all-beta family.
In particular

$$
\begin{aligned}
T_2&=\langle\beta,\alpha\rangle,&
T_3&=\langle T_2,\beta\rangle,&
T_4&=\langle T_3,T_2\rangle,\\
T_5&=\langle T_4,T_3\rangle
 =\big\langle
   \langle\langle\langle\beta,\alpha\rangle,\beta\rangle,
                \langle\beta,\alpha\rangle\rangle,
   \langle\langle\beta,\alpha\rangle,\beta\rangle
   \big\rangle.
\end{aligned}
\tag{76.7}
$$

Every repeated subtree in this expression is a distinct ordered occurrence;
the recurrence is a syntax identity, not a source-copy operation. Its
leaf and seam-depth recurrences are
$\ell_{n+2}=\ell_{n+1}+\ell_n$ and
$h_{n+2}=1+\max\{h_{n+1},h_n\}$, with
$\ell_0=\ell_1=1$ and $h_0=h_1=0$. They give

| $n$ | $\ell(T_n)$ | $h(T_n)$ | alpha leaves | beta leaves |
| --- | --- | --- | --- | --- |
| $0$ | $1$ | $0$ | $1$ | $0$ |
| $1$ | $1$ | $0$ | $0$ | $1$ |
| $2$ | $2$ | $1$ | $1$ | $1$ |
| $3$ | $3$ | $2$ | $1$ | $2$ |
| $4$ | $5$ | $3$ | $2$ | $3$ |
| $5$ | $8$ | $4$ | $3$ | $5$ |

Thus $\operatorname{Pos}(T_5)$ has fifteen source vertices, fourteen
inherited seams and sixteen distinct grounded stubs. Its eight ordered
leaf occurrences are

$$
\begin{array}{c|cccccccc}
p&LLLL&LLLR&LLR&LRL&LRR&RLL&RLR&RR\\ \hline
\operatorname{label}(p)&\beta&\alpha&\beta&\beta&\alpha&\beta&\alpha&\beta
\end{array}.
\tag{76.8}
$$

Choose a separate commission with immutable INITIAL $\alpha$ and one cap
$H=8$ fixed before execution. The five whole-rho candidates have leaf
counts $1,2,3,5,8$. Each passes the original whole-candidate guard
$\ell\le H$, including the first label-only acceptance and the final
equality. Hence the literal current source $T_5=\rho^5(\alpha)$ is
admitted by the unchanged source semantics at that cap. The same finite
prefix is legal at any separately predeclared fixed $H\ge8$. At $H=8$ a
subsequent thirteen-leaf candidate, if attempted, is refused, leaves
$T_5$ unchanged and supplies no candidate Read; Stop remains absorbing.
This establishes mathematical source admissibility, not a newly observed
native execution, acquired source authentication or an installed apparatus.

For this admitted source, Theorem76.2 would require $4\sqrt7<10$. Both sides
are positive, whereas

$$
(4\sqrt7)^2=112>100=10^2.
\tag{76.9}
$$

Therefore $E_2(\operatorname{Pos}(T_5))$ is impossible. No lower-cap
classification or assertion of a smallest counterexample follows.

**Corollary 76.4 (conditional minimum universal integer dimension).**
Relative to the commissioned template76.1 and the accepted ordinary
Proposition72.3, the minimum universal ambient integer dimension is three.
The same minimum holds for all legal finite source commissions at each
one fixed cap $H\ge8$.

**Proof.** In dimension one the height-zero hyperplane is a single point,
which cannot provide the two distinct ground tips required even by a
singleton. Dimension two fails for the separately legal source76.3.
Proposition72.3 supplies $E_s(D)$ for every authentic finite $D$ and
each fixed integer $s\ge3$, including its positive per-placement angle
and clearance margins and its prescribed reflected double. Consume that
construction directly. Its grounding
plane in three dimensions becomes the height-zero hyperplane in higher
dimensions. These facts prove the stated minimum, both over all separately
legal finite commissions and at any one fixed $H\ge8$. The quantifiers
are, for fixed $s$, every legal finite source followed by existence of its
own placement. They assert no simultaneous apparatus, no uniform
source/cap margin and no physical dimension law. $\square$

**Definition 76.5 (the unchanged historical witness and complete target).**
The separate cap-eight witness does not alter55.6/64.1. Their immutable
INITIAL is $T_2=\langle\beta,\alpha\rangle$, their original cap is
$H=3$, and their complete history remains

$$
\operatorname{Read}[BA];\quad\rho[\mathrm{accept}];\quad
\operatorname{Read}[A+B];\quad\rho[\mathrm{refuse}];\quad
\operatorname{Read}[A+B];\quad\operatorname{Stop}.
\tag{76.10}
$$

The initial, accepted and refused-candidate leaf counts are $2,3,5$.
Only $T_3=\langle\langle\beta,\alpha\rangle,\beta\rangle$ is installed
after acceptance; $T_4$ is refused without a candidate Read. INITIAL and
the original tag-one target $(1,(1,1),BA,A+B)$ remain unchanged. The
accepted five-port domain has ordered basis $(o,L,R,LL,LR)$. Both complete
ten-pair tables on precisely that source version remain

$$
\begin{array}{c|cccccccccc}
\{p,q\}&oL&oR&oLL&oLR&L\,R&L\,LL&L\,LR&R\,LL&R\,LR&LL\,LR\\ \hline
G_D^{\rm c}&1/2&1/2&1/4&1/4&1/4&3/8&3/8&1/8&1/8&3/16\\
G_D^{\rm k}&9/26&7/26&3/26&3/26&3/26&5/26&5/26&1/26&1/26&5/78
\end{array}.
\tag{76.11}
$$

These tables belong to that stopped cap-three history. They are not pair
tables for $T_5$, whose separate admissibility neither raises that history's
cap nor continues it after Stop. The complete prescriptions for arbitrary
authentic $D$ are still

$$
\begin{aligned}
G_D^{\rm c}(p,q)&=\langle e_p,L^{-1}e_q\rangle
 =\frac23\,2^{-d(p,q)}+\frac13\,2^{-(|p|+|q|)},\\
G_D^{\rm k}(p,q)&=\langle e_p,L_D^{-1}e_q\rangle,\qquad
\phi(p)=2^{-|p|},\\
d(p,q)&=|p|+|q|-2|p\wedge q|.
\end{aligned}
\tag{76.12}
$$

Here $L$ is55.2's infinite unit-conductance occurrence Laplacian, and
$L_D=I_D^*LI_D$ has diagonal two at the root, three elsewhere and
off-diagonal $-1$ on each inherited seam. Both entire kernels, including
their diagonals, retain their own boundary law. The common one-body field
is the same for both; killing the pair prescription does not replace it
by the newly solved killed one-body field. The two unequal prescriptions
remain separately commissioned operators, with no free physical switch
or single generator equal to both.

Definition64.5 remains literal. $X_D$ has every intrinsic unit seam and
both unit grounded stubs at every current leaf, with mass-one source
atoms, no ground atoms and fixed cable density $0<\delta\le1$:

$$
\mu_\delta=\sum_{p\in D}\delta_p+\delta\sum_e dx_e,\qquad
\mathcal K_{D,1}=L^2(X_D,\mu_\delta),\qquad
\mathcal K_{D,2}^{\rm hc}
 =\left[L^2((X_D^2)\setminus\Delta,
                    \mu_\delta\otimes\mu_\delta)\right]_{\rm sym}.
\tag{76.13}
$$

Here $\delta_p$ is a Dirac mass and $\Delta=\{(x,x):x\in X_D\}$ is the
actual same-position set.

All distinct atomic pairs, both orders of atom/cable slices, every
different-cable rectangle and both same-cable triangles remain, with
norm weights $1,\delta,\delta^2$. The form domains retain cable and
slice $H^1$, piecewise cell $H^1$, exchange symmetry, endpoint-to-atom
and cell-boundary-to-slice matching, zero ground traces in either
coordinate and both zero same-cable diagonal traces. Missing atomic
collision values are zero in slice endpoint conditions, including
shared-port collisions approached on different cables. No arbitrary
$H^1$ rectangle-corner value is introduced. The kinetic forms are
exactly64.7: each one-particle cable derivative and each two-particle
slice derivative has coefficient one; each cell's sum of the two
derivative energies has coefficient $\delta$, including both
same-cable triangles. Their operators carry the same commissioned
factor $a>0$.

With commissioned $a,g>0$ and $\nu\ge0$, the unchanged potentials are
$U_{D,1}=-g\phi_A$ and

$$
U_{D,2}^{\diamond}(x,y)
 =-g(\phi_A(x)+\phi_A(y))
  -\nu\mathbf1_{\{x=p,y=q\in D,\ p\ne q\}}G_D^\diamond(p,q),
\qquad \diamond\in\{\mathrm c,\mathrm k\},
\tag{76.14}
$$

where $\phi_A$ is $\phi$ on atoms and zero on open cables. The pair
term is exchange invariant and zero on every other stratum. Geometry
here changes none of these spaces, measures, forms, coefficients,
domains or traces, and supplies no new operator correspondence.

**Scope 76.6 (suppliers and remaining realization obligations).**
The literal recurrence and fixed-cap semantics are supplied by55.1 and
the original TM30/PR57 interface retained in60.1/66.1;72.3 supplies
higher-dimensional sufficiency. The new deduction is76.2's completed
planar interval proof and its authentic cap-qualified consequence76.3–76.4.
Euclidean convexity, the intermediate value theorem, connectedness after
tree-leaf deletion and finite interval packing are mature elementary
methods, applied explicitly above. No mathematical priority is claimed.
The analytic suppliers credited in64.9,67.10,72.1 and75.15 retain their
stated scopes: Bolte–Kerner's Lebesgue metric-graph contact forms,
Suzuki's qualified vacuum scaling, Cherednichenko–Ershova–Kiselev's
Neumann thinning theorem and Seiringer–Yin's distinct confined-boson
limit supply no additional planar necessity or native dimension law.

The band is essential to this numerical width floor. Without an upper
height gap below one, unit-ground widths can tend to zero. The broader
prescribed-metric planar problem72.13, with centre distances
$1+h_v(\varepsilon)+h_w(\varepsilon)$, both grounds at every leaf and
its clearance/port margins, remains unresolved. Those plate offsets
are neither source heights nor the seam depth $h(D)$. The analytic
separated-window logarithmic loss72.12 is a different limitation.
No perturbed-length theorem is asserted: unequal stubs can admit
same-side tips, and disjointness or uniform angle control would need
separate proofs. Satisfying the width inequality (76.3) is only necessary,
not a planar existence criterion. The intrinsic-length planar incidence
comparisons66.9/67.9 remain compatible with this Euclidean unit-length
obstruction.

All material clauses of66.10,67.11,68.7,71.2,72.13 and75.16 persist.
In particular retain immutable INITIAL, one original fixed cap,
source-independent actor initialization, all labels/brackets/order and
occurrences, actual versions and complete supplied contexts/candidates,
original guards, acceptances/refusals, destructive actions, numerical
Read, absorbing Stop and every actually acquired chronological record.
The original actor's arbitrary, unbounded or possibly zero $a$, untagged
radius-$7/25$ $b$ and jointly adversarial/history-dependent errors remain
distinct from the positive commissioned Hamiltonian parameters.
Whole-rho, beta-empty label changes and the separate Left/Right grafts
keep their root, degree, field, domain and dynamic covariance duties.

The complete field bank of67, all $2^H-1$ oscillator modes, excitations,
spectators, auxiliary factors and unknown particle/field/auxiliary
correlations remain in the full joint norm with the common reference
and actual clock. Retain separately $F_D^{\rm k}=L_D$ and
$F_D^{\rm c}=L_D-P_{\operatorname{Leaf}(D)}$, their identity extensions
on unused modes, balanced coordinate/momentum couplings and the on-site
self-energy compensation using the actual diagonal of the same inverse.
The field-number/moment ingress hypotheses and atom-only
displacement/domain boundary of67.3 remain material. Neither this
skeleton nor75's particle correspondence proves a nonzero coupled-field
thin-carrier comparison. No partial trace, vacuum restriction, reset,
cloning or calibrated-state re-preparation is licensed. Actual
local/isotropic mediation, stiffness and
compensation installation, unknown-state ingress/recovery/preparation,
source-owned switching, retained graft laws, native operation/metric
and Read/Stop correspondence still require their own supplied proofs.
The separately reported DEV native JointLaw is a source report on its
own carrier; correspondence with this spatial carrier is not established.

The common $\Pi$ of63.13 retains its full-vector/spanning and common-zero
hypotheses, whole quadratic-distance/positive-semidefinite Gram relation,
at least two independent directions, alternating bilinear exact-area/Jacobi
law, actual orthonormal probes, finite binary calibration and
hidden-kernel-preserving generators. Reference preparation/calibration,
actual clock conversion, original joint error handling, complete retained
complement and cross-block control, and usable finite execution/precision
certificates remain separate obligations.

All three acquisition contracts retain their distinct scopes. Section57's
immutable composition-promised endpoint contract keeps fixed depth caps,
common source-independent initialization, actual query/reply histories,
correct finite stopping on every promised positive and negative source,
distinct actual-address fees and no old-source archive. The paid
positive-root archive/exact nonadvancing-cut contract keeps its exact
port, finite stopping/decoding, protected records after refusal/closure,
aligned actual generation, trusted markers, no unrecorded source change,
closed strong ports and paid write/protect/retain/query rights; every
reply-affecting retained source influence belongs in its service price.
The phase-coherent full-tail contract keeps its once-sampled-depth actual
Read process and paid stopped transcript. None grants source copying,
reset, independent resampling, unknown-state preparation or an exact-limit
Read, nor transfers its radii, state counts, updates or clocks here.

The original spatial operation/metric bridge, packing, transverse,
exterior, leakage and collision controls remain to be supplied. Every
construction, acquisition, preparation, field/compensation/stiffness
installation, exclusion/repulsion control, switching, source service,
production, storage, hold, retention, maintenance and precision charge,
including service durations and total lifetime price, remains material.
Stratum counts, normalized measures and infinite-dimensional interval/cell
spaces supply no finite memory or resource advantage. This finite ordinary
result supplies no fresh kernel, native or physical validation and does
not complete the sustained why-three/source/native/field/acquisition/
resource programme.

## 76.99 追加锚（本行以下为增补区）
