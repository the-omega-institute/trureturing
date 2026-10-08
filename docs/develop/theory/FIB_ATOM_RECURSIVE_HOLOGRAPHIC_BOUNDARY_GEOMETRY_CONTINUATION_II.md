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
