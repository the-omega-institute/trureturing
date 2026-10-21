# FIB atomic recursive holographic boundary geometry VI: native state metrics and Markov transport

**Definition 0.1 (source and reference conventions).** The source algebra,
actual accepted substitution, acquired branch domain, occurrence forms and
birth incidence are those of
[Continuation IV, §§92--113](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md).
References numbered 92--113, including equations (112.1)--(112.9), refer
to that volume; numbers 114--123 refer to this volume. In IV (112.8),
$T_e$ maps born coordinates to born edges; the parent-copy $T_e$ of
Definition 115.1 below is a different, explicitly typed node-state map.
The counting generators of
[Continuation V, Definition 114.1 and §116](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_V.md)
retain their specified node norms. A successor state metric in §120
instead changes that norm while fixing the same original edge form.
All vector-space dimensions below count occurrence-state coordinates;
the occurrence distance is the original tree's shortest-path distance.

## 114. A finite-depth source-to-carrier certificate and its first failures

The finite occurrence and transport constructions above can be assembled into
one typed test object. This does not supply a physical realization; it records
which bridge clauses are already exact on a finite source and which ones fail
before any continuum interpretation is attempted. The family below includes the
singleton labels and the branch-root sources to which the native three-port
contract applies.

**Definition 114.1 (the finite-depth candidate bridge).** Let

$$
\mathcal S_n=\{\alpha,\beta\}
  \cup\{t=\langle s,u\rangle:\operatorname{height}(t)\le n\}
$$

be the finite ordered source family of height at most $n$. For $t\in
\mathcal S_n$, use its occurrence vertices $V_t$, oriented edge set $E_t$,
and the closed unit-edge operator $L_t=D_t^*D_t$. Define

$$
\begin{aligned}
d_t(x,y)&=\text{the shortest-path length in }(V_t,E_t),\\
\mu_t(x)&=1,\\
\widehat\mu_t(x)&=N_t^{-1},\\
U_t&=-D_tL_t^{+1/2}:P_t\ell^2(V_t)\longrightarrow\ell^2(E_t),
\end{aligned}
\tag{114.1}
$$

where $P_t$ removes constants. The tagged carrier is

$$
\mathscr C_n
  =\bigsqcup_{t\in\mathcal S_n}
     \bigl(\{t\}\times V_t,\{t\}\times E_t,d_t,\mu_t,U_t\bigr).
\tag{114.2}
$$

The tag is part of the mathematical carrier in (114.2); it is not declared to
be a freely available observation. A coarse port projection instead retains
only the entry data

$$
\pi^{\rm port}_t
  =\bigl(N_t,\ |B_t|,\ K_t\bigr),
\qquad K_t=R_tL_tR_t^*,
\tag{114.3}
$$

with the three literal ports $(\varepsilon,L,R)$ whenever they are reached.
For the port projection and its matrix, restrict to the branch-root subfamily
where these three ports are present; the full tagged carrier continues to
include singleton sources and sources with other root labels.

**Proposition 114.2 (finite exactness and the first bridge failures).** The
candidate (114.1)--(114.3) has the following properties.

1. Every object is finite and typed. For the Fibonacci sources $T_n$, the
   maps $U_{T_n}$ are the unitaries of Theorem 103.2, including the full
   root-invisible eigenspaces. Thus a finite occurrence carrier can preserve
   the complete finite operator, rather than only its root spectral measure.

2. The recursive birth map is pointwise local: under the old/new decomposition,

   $$
   V_{\rho t}=\iota_t(V_t)\sqcup B_t,
   \qquad
   E_{\rho t}=\iota_t^E(E_t)\sqcup
      \{(p,p\sigma):p\sigma\in B_t\},
   \tag{114.4}
   $$

   so every new edge has unit distance from its parent. This is only a local
   incidence statement. The one-step action changes all beta-parent sites at
   once and

   $$
   |B_t|=2|M_t|,
   \tag{114.5}
   $$

   so there is no source-independent bound on the number of changed sites.

3. Coarse port data are not action-closed. The two sources

   $$
   x=\langle\alpha,\beta\rangle,
   \qquad y=\langle\beta,\alpha\rangle
   $$

   have the same (114.3) at entry, while the successor port matrices have
   diagonal entries $(2,1,3)$ and $(2,3,1)$, respectively. Hence no update
   map on $\pi^{\rm port}_t$ can represent the native Apply operation. This is
   the B1 failure for the coarse observation, already witnessed by
   Proposition 112.4a.

4. The literal zero-extension of node states is not operator-compatible. In
   the decomposition of (114.4), the exact block formula of (112.9) gives

   $$
   L_{\rho t}J_tf-J_tL_tf
     =(2H_tf)\oplus(-C_t^*f).
   \tag{114.6}
   $$

   If $M_t\ne\varnothing$, choosing $f$ nonzero at a beta parent makes the
   right-hand side nonzero. Therefore $J_t$ does not intertwine the closed
   Laplacians or their heat semigroups. The source recursion is exact, but the
   simplest ancestry extension fails the operator part of B6. This calculation
   does not by itself settle B7, whose separate requirement is that the graph
   edges arise from actual source seams and transport relations.

5. The literal unit-edge counting measure is not globally 3-Ahlfors regular on
   the Fibonacci family. The source height obeys

   $$
   \operatorname{height}(T_n)=n-1\quad(n\ge1),
   \qquad N_{T_n}=2F_{n+1}-1.
   \tag{114.7}
   $$

   Consequently $B_{d_{T_n}}(r,2n-2)=V_{T_n}$, and

   $$
   \mu_{T_n}\bigl(B_{d_{T_n}}(r,2n-2)\bigr)=2F_{n+1}-1.
   \tag{114.8}
   $$

   A uniform upper bound $\mu(B(r,R))\le CR^3$ for all $n$ and all radii
   reaching the source diameter would imply

   $$
   2F_{n+1}-1\le C(2n-2)^3,
   $$

   which is impossible because $F_{n+1}$ grows exponentially. Thus B5 fails
   for this literal metric and counting measure at global scales. A bounded
   small-radius window, a rescaled edge metric, or a different measure remains
   a separate bridge choice; none is supplied by (114.1).

**Proof.** Items 1--4 are Theorems 103.2 and 112.4 together with the block
identity (112.9) and the explicit two-source witness of Proposition 112.4a.
For item 5, the height recurrence follows from
$T_n=\langle T_{n-1},T_{n-2}\rangle$, with heights $0,0$ at $n=0,1$,
and the node-count recurrence is Theorem 92.3. The ball of radius $2n-2$
contains every occurrence because every root-to-node path has length at most
$n-1$. Finally $F_{n+1}$ dominates a geometric progression along every
other index, so it cannot be bounded by a cubic polynomial in $n$. $\square$

The certificate separates three different repairs. Preserving the source tag
or a sufficient history can repair B1; a corrected state-dependent transport,
if one exists under the declared permissions, is needed for B6, while B7 needs
separate source-seam provenance; and a scale window or renormalized
metric/measure is needed before a volume statement can be compared with
dimension three. The finite unitary $U_t$ alone repairs
none of these gaps and does not produce a smooth rank-three distribution.

Thus the first finite-depth bridge test has a concrete outcome: the native
occurrence carrier is an exact finite spectral object, pointwise births are
local, but coarse action descent, zero-extension heat compatibility and global
three-dimensional volume growth all fail under the literal choices above. The
remaining continuum bridge must choose which information and which scale are
preserved before B2--B7 can be evaluated jointly.

## 114.99 追加锚（本行以下为增补区）

## 115. Parent-copy form transport and the generator obstruction

The first failure in §114 does not mean that every transport across a birth
step is impossible. It separates two requirements that are often conflated:
preserving the edge-energy form and intertwining the node generator. The
block identities of §112 give an exact finite test of this distinction.

**Definition 115.1 (the parent-copy extension).** In the old/new decomposition
of (112.7), define

$$
T_e:\ell^2(V_e)\longrightarrow\ell^2(V_{e+1}),
\qquad
T_ef=\begin{pmatrix}f\\ C_e^*f\end{pmatrix},
\tag{115.1}
$$

so every newly born child receives the value of its parent. Let $J_e$ retain
only the old coordinates, as in (112.8). More generally, write a top-fixed
linear extension as

$$
S_Qf=\begin{pmatrix}f\\Qf\end{pmatrix},
\tag{115.2}
$$

where $Q:\ell^2(V_e)\to\ell^2(B_e)$ is arbitrary.

**Theorem 115.2 (unique form transport, but no generator descent).** For every
finite source step, the parent-copy map satisfies

$$
D_{e+1}T_e=
\begin{pmatrix}D_e\\0\end{pmatrix},
\qquad
T_e^*L_{e+1}T_e=L_e,
\tag{115.3}
$$

and it is the unique top-fixed linear extension $S_Q$ with
$S_Q^*L_{e+1}S_Q=L_e$. It also obeys

$$
L_{e+1}T_e=J_eL_e,
\qquad
T_eL_e-L_{e+1}T_e=
\begin{pmatrix}0\\C_e^*L_e\end{pmatrix}.
\tag{115.4}
$$

Consequently, whenever $C_e^*L_e\ne0$, no top-fixed form-preserving
extension can intertwine the node generators. In the witness source
$x=\langle\alpha,\beta\rangle$, taking $f=\delta_R$ gives
$C_e^*L_ef=(1,1)$, so the obstruction is already present at the first
nontrivial birth step.

The extension is also not an isometry for the counting node inner products:

$$
\|T_ef\|^2
=\|f\|^2+\|C_e^*f\|^2
=\|f\|^2+2\|H_ef\|^2.
\tag{115.5}
$$

Thus a parent-copy map preserves the edge form while changing node mass on
beta-parent coordinates. Positive child weights, a time change, or a different
state norm would have to be declared before it could represent the same heat
response.

**Proof.** For an arbitrary $S_Q$, (112.8) gives

$$
D_{e+1}S_Qf=
\begin{pmatrix}D_ef\\(Q-C_e^*)f\end{pmatrix}.
\tag{115.6}
$$

Therefore

$$
\langle S_Qf,L_{e+1}S_Qf\rangle
=\|D_ef\|^2+\|(Q-C_e^*)f\|^2.
\tag{115.7}
$$

Equality with the old form for every $f$ forces $Q=C_e^*$, proving
uniqueness and the first identity in (115.3). Applying the adjoint block in
(112.9) to (115.3) gives
$L_{e+1}T_e=(L_ef,0)=J_eL_ef$, and multiplication on the right by $L_e$
gives the second identity in (115.4). For the witness $x$, the old Laplacian
sends $\delta_R$ to $(-1,0,1)$, while $C_e^*$ duplicates the value at the
beta parent $R$, yielding $(1,1)$. Finally
$C_eC_e^*=2H_e$ proves (115.5). \(\square\)

The result gives a precise B6 split. A form-level recursive carrier can be
made exact by copying parent values, but the same map does not carry the
counting-measure heat semigroup forward. A successful continuum bridge must
therefore choose which response is preserved and supply the corresponding
measure, clock and boundary readout. This finite obstruction neither selects a
physical dimension nor proves that every state-dependent transport fails; it
only rules out the top-fixed, form-preserving, generator-intertwining choice.

## 115.99 追加锚（本行以下为增补区）

## 116. Positive-mass no-go for simultaneous form, norm, and generator transport

The parent-copy result leaves one possible repair question: can a positive
node measure make the same transport both norm-preserving and dynamically
compatible? The answer is negative if the old coordinates are fixed and the
clock is unchanged.

**Definition 116.1 (weighted node generators).** Let \(\mathsf G_e\) and
\(\mathsf G_{e+1}\) be strictly positive diagonal (all diagonal entries \(>0\))
mass matrices on \(V_e\) and \(V_{e+1}\).
Write

$$
A_e=D_e^*D_e,\qquad
\mathcal L_e=\mathsf G_e^{-1}A_e,
\tag{116.1}
$$

and similarly for \(e+1\). Consider a top-fixed extension \(S_Q\) from (115.2).
The three requirements are:

$$
\begin{array}{ll}
\text{(F)}&S_Q^*A_{e+1}S_Q=A_e
     \quad\text{(edge-form preservation)},\\
\text{(N)}&S_Q^*\mathsf G_{e+1}S_Q=\mathsf G_e
     \quad\text{(node-norm preservation)},\\
\text{(G)}&\mathcal L_{e+1}S_Q=S_Q\mathcal L_e
     \quad\text{(same-clock generator intertwining)}.
\end{array}
\tag{116.2}
$$

**Theorem 116.2 (positive-mass obstruction).** Suppose the old tree is
connected and nontrivial, and \(B_e\ne\varnothing\). There is no top-fixed
linear extension \(S_Q\) and no strictly positive diagonal \(\mathsf G_{e+1}\)
satisfying
all three conditions (F), (N), and (G).

**Proof.** Condition (F) and Theorem 115.2 force \(Q=C_e^*\), so
\(S_Q=T_e\). The block identity (115.4) gives

$$
A_{e+1}T_e=J_eA_e.
\tag{116.3}
$$

Taking the old-coordinate block of (G) yields

$$
(\mathsf G_{e+1}^{-1})_{\mathrm{old}}A_e=\mathsf G_e^{-1}A_e.
\tag{116.4}
$$

Every row of \(A_e\) is nonzero in a connected nontrivial tree; applying
(116.4) to a basis vector at each vertex therefore forces
\((\mathsf G_{e+1})_{\mathrm{old}}=\mathsf G_e\). But then the old/child block decomposition
of the norm in (N) gives

$$
T_e^*\mathsf G_{e+1}T_e
 =\mathsf G_e+C_e(\mathsf G_{e+1})_{\mathrm{child}}C_e^*.
\tag{116.5}
$$

The second term is a nonzero positive diagonal matrix whenever
\(B_e\ne\varnothing\), contradicting (N). \(\square\)

For the witness \(x=\langle\alpha,\beta\rangle\), this contradiction is
visible without a general argument: the two new child masses add a strictly
positive contribution to the old beta-parent coordinate after the unique
form-preserving copy. A time-rescaled condition
\(\mathcal L_{e+1}S_Q=\lambda_eS_Q\mathcal L_e\), a non-top-fixed transport,
or a non-diagonal state metric is outside Theorem 116.2 and must be declared
as a new bridge choice. The theorem therefore closes one exact option while
leaving those relaxed options open; it does not prove a universal transport
no-go or select a physical dimension.

## 116.99 追加锚（本行以下为增补区）

## 117. Scalar clock rescaling does not repair the positive-mass obstruction

The remaining scalar-clock option can be tested without assuming the full
child-coordinate response. This makes the obstruction stronger: if even the
old-coordinate generator is required to run at one common rescaled clock, the
form and norm requirements are already incompatible.

**Definition 117.1 (old-coordinate scalar-clock transport).** Keep the
top-fixed extension and the three requirements (F) and (N) of Definition
116.1. For a scalar \(\lambda_e>0\), replace (G) by the weaker condition

$$
\boxed{
J_e^*\mathcal L_{e+1}S_Q
   =\lambda_e\mathcal L_e.
}
\tag{117.1}
$$

The full rescaled intertwining condition

$$
\mathcal L_{e+1}S_Q
   =\lambda_eS_Q\mathcal L_e
\tag{117.2}
$$

implies (117.1), because \(J_e^*S_Q=I\). Thus a no-go for (117.1) also
rules out the full scalar-clock repair.

**Theorem 117.2 (scalar-clock no-go).** Suppose \(B_e\ne\varnothing\),
\(\mathsf G_e\) is strictly positive diagonal, and the old tree has at least one vertex
outside the beta-parent set \(M_e\). There is no top-fixed linear extension
\(S_Q\) and no strictly positive diagonal \(\mathsf G_{e+1}\) satisfying (F), (N), and
(117.1), for any \(\lambda_e>0\).

**Proof.** By (F), Theorem 115.2 forces \(S_Q=T_e\). Write the strictly
positive child block of \(\mathsf G_{e+1}\) as \(\mathsf G_c\), and its old
block as \(\mathsf G_o\). From
\(A_{e+1}T_e=J_eA_e\), the old-coordinate part of (117.1) is

$$
\mathsf G_o^{-1}A_e=\lambda_e\mathsf G_e^{-1}A_e.
\tag{117.3}
$$

Every row of \(A_e\) is nonzero on a connected nontrivial tree. Since the
left factor in (117.3) is diagonal, each row therefore gives

$$
\mathsf G_o^{-1}=\lambda_e\mathsf G_e^{-1},
\qquad
\mathsf G_o=\lambda_e^{-1}\mathsf G_e.
\tag{117.4}
$$

The norm condition (N), together with \(T_e=(I,C_e^*)^{\mathsf T}\), now
requires

$$
C_e\mathsf G_cC_e^*
   =(1-\lambda_e^{-1})\mathsf G_e.
\tag{117.5}
$$

The left side is supported on \(M_e\). At a vertex \(r\notin M_e\), its
\(r,r\) entry is zero, whereas the right side is
\((1-\lambda_e^{-1})\mathsf G_e(r,r)\). Strict positivity of \(\mathsf G_e(r,r)\) forces
\(\lambda_e=1\). Substituting this into (117.5) gives

$$
C_e\mathsf G_cC_e^*=0,
$$

which is impossible: \(B_e\ne\varnothing\), \(\mathsf G_c>0\), and every born child
contributes its positive mass to its beta parent. Hence no such scalar clock
exists. \(\square\)

For every native FIB birth with a nonempty child set, the root is a branch
vertex and is therefore outside \(M_e\); the stated support hypothesis is
thus met in the nontrivial birth steps considered here. The first witness
\(\langle\alpha,\beta\rangle\) makes the calculation explicit: with the
ordered old vertices \((\varepsilon,L,R)\),

$$
C_e\mathsf G_cC_e^*
   =\operatorname{diag}(0,0,m_{RL}+m_{RR}),
\qquad m_{RL},m_{RR}>0.
\tag{117.6}
$$

The root entry forces \(\lambda_e=1\), while the \(R,R\) entry then remains
strictly positive, contradicting (117.5). An exact symbolic multiplication
also gives \(A_{e+1}T_e=J_eA_e\) and
\(C_e^*A_e\ne0\) for this witness. The latter shows that the child block of
the stronger full condition (117.2) fails independently as well, since it
would require

$$
0=\lambda_eC_e^*\mathcal L_e.
\tag{117.7}
$$

The result closes the single global scalar-clock repair while leaving the
actual alternatives explicit: a nonuniform clock, a transport that does not
fix all old coordinates, or a non-diagonal state metric changes the bridge
problem and is not covered by this theorem. It still does not prove a
universal transport no-go or select a physical dimension.

## 117.99 追加锚（本行以下为增补区）

## 118. The surviving nonuniform clock has a mass-budget profile

The scalar no-go does not justify declaring every clock repair impossible.
The next weaker candidate is a node-dependent clock on the retained old
coordinates. Its exact algebra identifies what a successful bridge would
have to pay for.

**Definition 118.1 (old-coordinate diagonal clock).** Let
\(\Lambda_e=\operatorname{diag}(\lambda_e(p))\) be a strictly positive
diagonal operator (all \(\lambda_e(p)>0\)) on \(\ell^2(V_e)\). Replace the
scalar condition (117.1) by

$$
\boxed{
J_e^*\mathcal L_{e+1}S_Q
   =\Lambda_e\mathcal L_e.
}
\tag{118.1}
$$

This is still only an old-coordinate response condition. A full
node-dependent intertwining condition would also constrain the child block
and is strictly stronger.

**Theorem 118.2 (necessary profile for a diagonal clock).** Assume the old
tree is connected and nontrivial, \(B_e\ne\varnothing\), and \(\mathsf G_e\) and
\(\mathsf G_{e+1}\) are strictly positive diagonal. If (F), (N), and (118.1) hold, then
\(S_Q=T_e\), and, writing

$$
\mathsf G_{e+1}=
\begin{pmatrix}\mathsf G_o&0\\0&\mathsf G_c\end{pmatrix},
\qquad \mathsf G_c>0,
$$

one necessarily has

$$
\boxed{
\mathsf G_o=\mathsf G_e\Lambda_e^{-1},
\qquad
C_e\mathsf G_cC_e^*
   =\mathsf G_e(I-\Lambda_e^{-1}).
}
\tag{118.2}
$$

Consequently:

1. every old vertex outside \(M_e\) has \(\lambda_e(p)=1\);
2. every beta parent \(p\in M_e\) must satisfy

   $$
   m_{pL}+m_{pR}<m_e(p),
   \qquad
   \lambda_e(p)
   =
   \frac{m_e(p)}
        {m_e(p)-m_{pL}-m_{pR}},
   \tag{118.3}
   $$

   where \(m_e(p)=\mathsf G_e(p,p)\) and
   \(m_{p\sigma}=\mathsf G_c(p\sigma,p\sigma)\).

**Proof.** Condition (F) again forces \(S_Q=T_e\). Using
\(A_{e+1}T_e=J_eA_e\), the old-coordinate part of (118.1) becomes

$$
\mathsf G_o^{-1}A_e=\Lambda_e\mathsf G_e^{-1}A_e.
\tag{118.4}
$$

Every row of \(A_e\) is nonzero, so the diagonal factors in (118.4) agree
row by row:

$$
\mathsf G_o^{-1}=\Lambda_e\mathsf G_e^{-1},
\qquad
\mathsf G_o=\mathsf G_e\Lambda_e^{-1}.
\tag{118.5}
$$

The norm identity (N) is

$$
\mathsf G_o+C_e\mathsf G_cC_e^*=\mathsf G_e.
\tag{118.6}
$$

Substitution gives the second equation of (118.2). Since
\(C_e\mathsf G_cC_e^*\) is supported exactly on beta-parent coordinates and its
diagonal entry at \(p\in M_e\) is \(m_{pL}+m_{pR}\), (118.3) follows.
Positivity of \(\Lambda_e\) requires the denominator in (118.3) to be
positive. At every \(p\notin M_e\), the left side of the second equation in
(118.2) is zero, so positivity of \(m_e(p)\) forces
\(\lambda_e(p)=1\). \(\square\)

The first witness \(x=\langle\alpha,\beta\rangle\) exposes the profile
without any abstraction. With old order
\((\varepsilon,L,R)\), the two children \(RL,RR\) are born at the single
beta parent \(R\), and

$$
C_e\mathsf G_cC_e^*
   =\operatorname{diag}(0,0,m_{RL}+m_{RR}).
\tag{118.7}
$$

Thus \(\lambda_e(\varepsilon)=\lambda_e(L)=1\), while

$$
\lambda_e(R)
   =\frac{m_R}{m_R-m_{RL}-m_{RR}}.
\tag{118.8}
$$

For the literal counting measure,
\(m_\varepsilon=m_L=m_R=m_{RL}=m_{RR}=1\), so (118.8) has a negative
denominator. Hence a positive diagonal node-dependent clock cannot repair
the counting-measure transport even after the global scalar restriction is
removed.

For a general positive mass assignment, (118.3) leaves a genuine but narrow
bridge candidate: every beta parent must reserve enough old mass to pay for
both children, and the clock must speed up precisely on those parent
coordinates. The condition is necessary, not sufficient. In particular,
the full transport equation still has the child-block obstruction
\(0=\Lambda_{e+1,\mathrm{child}}C_e^*\mathcal L_e\) whenever its child
response is required. A successful realization would therefore need both a
mass profile satisfying (118.3) and a separate rule for the newly born
coordinates. This result does not establish such a realization, and it
does not select a physical dimension.

## 118.99 追加锚（本行以下为增补区）

## 119. Full child-coordinate target-clock obstruction on the finite raw carrier

The displayed old-only equation (118.1) leaves the child coordinates outside
its equation. The full equation has a direct finite obstruction once the clock
is placed on the target side. Use \(\mathsf G_e\) and \(\mathsf G_{e+1}\) for
strictly positive diagonal matrices (all node-mass entries \(>0\)), reserving
\(M_e\) for the beta-parent set of (112.6).
Write

$$
\mathcal L_e=\mathsf G_e^{-1}L_e,
\qquad
\mathcal L_{e+1}=\mathsf G_{e+1}^{-1}L_{e+1},
\qquad
\mathsf G_{e+1}=\operatorname{diag}(\mathsf G_o,\mathsf G_c).
\tag{119.1}
$$

**Theorem 119.1 (target-side diagonal-clock no-go).** Let \(B_e\ne\varnothing\),
let \(S_Qf=(f,Qf)\) be top-fixed, and require edge-form preservation

$$
S_Q^*L_{e+1}S_Q=L_e.
\tag{119.2}
$$

If \(C_e^*L_e\ne0\), there are no strictly positive diagonal mass matrices in
(119.1) and no strictly positive diagonal output clock

$$
\Lambda_{e+1}=\operatorname{diag}(\Lambda_o,\Lambda_c),
\qquad\text{all diagonal entries \(>0\)}
$$

such that the full target-side equation

$$
\boxed{\mathcal L_{e+1}S_Q
       =\Lambda_{e+1}S_Q\mathcal L_e}
\tag{119.3}
$$

holds. Here \(\Lambda_{e+1}\) is target-side: equivalently
\(\Lambda_{e+1}^{-1}\mathcal L_{e+1}S_Q=S_Q\mathcal L_e\).
A domain-side clock equation such as
\(\mathcal L_{e+1}S_Q=S_Q\Lambda_e\mathcal L_e\) is a different,
unanalysed contract. The displayed target clock has strictly positive diagonal
blocks, so it is invertible. The theorem applies to this block-diagonal class;
block-mixing, non-diagonal block clocks, or singular clocks and non-diagonal
state metrics are outside its scope. For the raw unweighted occurrence object
\(\mathcal O_e\) of (112.4), set
\(\mathsf G_e=\mathsf G_{e+1}=I\); the same requirement is literally

$$
\boxed{L_{e+1}S_Q=\Lambda_{e+1}S_QL_e}.
\tag{119.3a}
$$

The mass-weighted equation (119.3) and this raw special case have the same
child-block obstruction.

A connected nontrivial old tree with a nonempty beta-parent set is a
sufficient condition for the nonzero hypothesis \(C_e^*L_e\ne0\): each
beta-parent row of its tree Laplacian is nonzero, and \(C_e^*\) duplicates that
row on its two children.

**Proof.** By (119.2), the parent-copy uniqueness of Theorem 115.2 gives
\(Q=C_e^*\) and \(S_Q=T_e\). Reuse its exact identity

$$
A_e:=D_e^*D_e=L_e,\qquad
A_{e+1}T_e=J_eA_e
\quad\text{equivalently}\quad
L_{e+1}T_e=J_eL_e.
\tag{119.4}
$$

Taking the old and child blocks of (119.3), with
\(\mathsf G_{e+1}=\operatorname{diag}(\mathsf G_o,\mathsf G_c)\), gives

$$
\begin{pmatrix}\mathsf G_o^{-1}L_e\\0\end{pmatrix}
=
\begin{pmatrix}
\Lambda_o\mathcal L_e\\
\Lambda_cC_e^*\mathcal L_e
\end{pmatrix}.
\tag{119.5}
$$

The child block forces
\(\Lambda_cC_e^*\mathcal L_e=0\). Positivity makes \(\Lambda_c\) invertible,
while multiplication by the strictly positive diagonal \(\mathsf G_e^{-1}\) only
rescales each duplicated parent row. Hence \(C_e^*\mathcal L_e=0\) is
equivalent to \(C_e^*L_e=0\), contradicting the hypothesis. No node-norm
condition (N) is used; retaining (N) therefore gives only an a fortiori
stronger impossibility. \(\square\)

**Corollary 119.2 (the first finite witness).** For
\(x=\langle\alpha,\beta\rangle\), order the old vertices as
\((\varepsilon,L,R)\). The old star Laplacian and the child restriction are

$$
L_e=
\begin{pmatrix}
2&-1&-1\\
-1&1&0\\
-1&0&1
\end{pmatrix},
\qquad
C_e^*=\begin{pmatrix}0&0&1\\0&0&1\end{pmatrix},
$$

so

$$
C_e^*L_e=
\begin{pmatrix}-1&0&1\\-1&0&1\end{pmatrix}\ne0.
\tag{119.6}
$$

The beta-parent row is duplicated on \(RL,RR\), and
\(C_e^*L_e\delta_R=(1,1)^{\mathsf T}\). Thus the full child response is
already impossible at this finite birth step under Theorem 119.1.

The exact escape boundaries are: the old-only condition (118.1), which does
not constrain the child block; a transport that is not top-fixed or does not
preserve the edge form; a domain-side clock; clocks or state metrics outside
the strictly positive block-diagonal old/child class (including block-mixing or
singular cases); an empty birth or \(C_e^*L_e=0\); and a quotient task whose
specification omits the child-sensitive response. A quotient inherits this
no-go only when its task preserves that response and the full equation descends
to the quotient. This finite result only closes the raw full-child target-clock
branch: it supplies no positive three-dimensional metric, volume, or spectral-
dimension condition, and does not assert a physical realization.

## 119.99 追加锚（本行以下为增补区）

## 120. All state metrics for the native parent-copy transport

**Definition 120.1 (fixed form, fixed old norm and full generator).** Fix
one actual accepted step from an arbitrary finite native source, using the
occurrences, births and unit-edge forms of IV Definition 112.2. Write
$V=V_e$, $B=B_e$, $n=|V|$, $k=|B|$, $L=L_e$, $L'=L_{e+1}$ and
$P=C_e^*$, with old coordinates first. Thus $P_{cx}=1$ exactly when
$x=\operatorname{par}(c)$, and

$$
L'=\begin{pmatrix}L+P^{\mathsf T}P&-P^{\mathsf T}\\-P&I_k\end{pmatrix},
\qquad T=\begin{pmatrix}I_n\\P\end{pmatrix},\qquad
L'T=\begin{pmatrix}L\\0\end{pmatrix}.
\tag{120.1}
$$

Fix the old norm $G=\operatorname{diag}(g_x:x\in V)$ with every $g_x>0$.
Set $g=G\mathbf1_n$, $h=\mathbf1_n^{\mathsf T}G\mathbf1_n$ and
$A=G^{-1}L$. A successor state metric is an arbitrary real symmetric
positive-definite matrix $\mathsf M$ on $\mathbb R^{V\sqcup B}$;
its entries need not be a node measure or nonnegative. Its positive
generator is $\mathcal A=\mathsf M^{-1}L'$. The exact requirements are

$$
T^{\mathsf T}L'T=L,\qquad T^{\mathsf T}\mathsf M T=G,\qquad
\mathcal A T=TA.
\tag{120.2}
$$

The last equality is on every old signed field and every successor
coordinate, at the same time parameter. On this finite space it also
implies $e^{-t\mathcal A}T=Te^{-tA}$ for all $t\ge0$ by the exponential
series. A top-fixed linear extension satisfying the first equality is
necessarily this $T$, by Theorem 115.2.

**Theorem 120.2 (complete native state-metric class).** Suppose $k>0$.
All and only the metrics satisfying (120.2) are the following matrices,
parametrized uniquely by $q\in\mathbb R^k$ and a symmetric $K\succ0$:

$$
\begin{aligned}
Z&=K^{-1}+hqq^{\mathsf T},\qquad
\mathsf W=\begin{pmatrix}I_n&0\\P&I_k\end{pmatrix},\\
\mathsf M&=\mathsf W^{-\mathsf T}
 \begin{pmatrix}G&gq^{\mathsf T}\\qg^{\mathsf T}&Z\end{pmatrix}
 \mathsf W^{-1}\\
&=\begin{pmatrix}
G-gq^{\mathsf T}P-P^{\mathsf T}qg^{\mathsf T}+P^{\mathsf T}ZP
 &gq^{\mathsf T}-P^{\mathsf T}Z\\
qg^{\mathsf T}-ZP&Z
\end{pmatrix}.
\end{aligned}
\tag{120.3}
$$

In particular the class is nonempty for every fixed positive diagonal
$G$, including every nontrivial branch in the full native domain $D$ of
IV (112.1). With $a=Kq$, $b=P^{\mathsf T}a$ and
$R=K-\mathbf1_k a^{\mathsf T}$, the full generator is

$$
\mathcal A=
\begin{pmatrix}
A+\mathbf1_n b^{\mathsf T}&-\mathbf1_n a^{\mathsf T}\\
PA-RP&R
\end{pmatrix},\qquad \mathcal A\mathbf1_{n+k}=0.
\tag{120.4}
$$

**Proof.** Reuse the native identities (120.1), rather than changing
the birth form. The coordinates $\mathsf W(f,z)=(f,Pf+z)$ give

$$
\mathsf W^{\mathsf T}L'\mathsf W
 =\begin{pmatrix}L&0\\0&I_k\end{pmatrix},\qquad
\mathsf W^{-1}T=\begin{pmatrix}I_n\\0\end{pmatrix}.
\tag{120.5}
$$

The norm condition fixes the upper-left block of
$\widetilde{\mathsf M}=\mathsf W^{\mathsf T}\mathsf M\mathsf W$ to $G$.
Write its other blocks as $X,X^{\mathsf T},Z$. The full generator
condition, multiplied by $\widetilde{\mathsf M}$, is exactly

$$
\begin{pmatrix}G&X\\X^{\mathsf T}&Z\end{pmatrix}
\begin{pmatrix}G^{-1}L\\0\end{pmatrix}
=\begin{pmatrix}L\\0\end{pmatrix},
\qquad X^{\mathsf T}G^{-1}L=0.
\tag{120.6}
$$

The old occurrence tree is connected, so
$\ker L=\mathbb R\mathbf1_n$. Hence each row of
$X^{\mathsf T}G^{-1}$ is a multiple of $\mathbf1_n^{\mathsf T}$;
equivalently $X=gq^{\mathsf T}$ for a unique $q$. This includes $n=1$,
where $L=0$ and every row of a one-column matrix has this form.

The standard positive-definite Schur-complement and block-inverse
identities are used here as ingredients: Boyd--Vandenberghe,
[*Convex Optimization*, Appendix A.5.5, printed p. 650](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf),
with the existing [bibliographic entry](../../../Library/QuadraticForms/boydvandenberghe2004convex.md).
For these particular blocks the Schur complement is
$Z-X^{\mathsf T}G^{-1}X=Z-hqq^{\mathsf T}$. It is positive definite
exactly when it equals $K^{-1}$ for a unique $K\succ0$. Congruence by
the invertible $\mathsf W$ proves both necessity and sufficiency in
(120.3). Inverting these blocks gives

$$
\widetilde{\mathsf M}^{-1}
=\begin{pmatrix}
G^{-1}+\mathbf1_n(q^{\mathsf T}Kq)\mathbf1_n^{\mathsf T}
 &-\mathbf1_n q^{\mathsf T}K\\
-Kq\mathbf1_n^{\mathsf T}&K
\end{pmatrix}.
\tag{120.7}
$$

Since $\mathbf1_n^{\mathsf T}L=0$, its product with the form in
(120.5) is $\left(\begin{smallmatrix}A&-\mathbf1_n a^{\mathsf T}\\0&K\end{smallmatrix}\right)$.
Conjugating back by $\mathsf W$ yields (120.4). Finally
$P\mathbf1_n=\mathbf1_k$ and $A\mathbf1_n=0$ give the displayed
zero row sums. The proof uses the standard matrix identities only to
classify this fixed native transport problem. $\square$

## 120.99 追加锚（本行以下为增补区）

## 121. Conservative Markov compatibility on the full native branch domain

**Definition 121.1 (Markov and original-edge support).** In the original
occurrence coordinates, a conservative Markov rate matrix is
$Q=-\mathcal A$ with $Q\mathbf1=0$ and $Q_{xy}\ge0$ for $x\ne y$.
It acts on column vectors of functions; row distributions evolve by
$\pi(t)=\pi(0)e^{tQ}$. Original-edge support means $Q_{xy}=0$ whenever
$x\ne y$ and $\{x,y\}\notin E_{e+1}$; rates on some original edges
may vanish. Irreducibility means that the directed graph of strictly
positive off-diagonal rates is strongly connected. For any such finite
$Q$, choosing $r\ge\max_x(-Q_{xx})$ makes $Q+rI$ entrywise
nonnegative, so $e^{tQ}=e^{-rt}e^{t(Q+rI)}$ is nonnegative and has
row sums one. Thus the sign convention specifies actual finite Markov
semigroups, not just conservation of constants.

**Theorem 121.2 (necessary and sufficient native Markov class).** Let the
old source be any branch in $D$, with at least one beta leaf and hence
$k>0$. For the entire class of Theorem 120.2, $Q=-\mathcal A$ is
conservative Markov if and only if $q=0$ and, after grouping each born
sibling pair $B_p=\{pL,pR\}$, $K$ is block diagonal with blocks

$$
K_p=\begin{pmatrix}d_p+s_{pL}&-d_p\\-d_p&d_p+s_{pR}\end{pmatrix},
\qquad d_p\ge0,\qquad s_{pL},s_{pR}\ge g_p^{-1}.
\tag{121.1}
$$

Every parameter choice in (121.1) is admissible and $K\succ0$.
Writing $Z=K^{-1}$, all these metrics are exactly

$$
\mathsf M=
\begin{pmatrix}G+P^{\mathsf T}ZP&-P^{\mathsf T}Z\\-ZP&Z\end{pmatrix}.
\tag{121.2}
$$

Let $v(p)$ be the unique old neighbour of a beta leaf $p$. The complete
list of off-diagonal rates is

$$
\begin{aligned}
Q_{xy}&=g_x^{-1} &&(x,y\in V,\ \{x,y\}\in E_e),\\
Q_{c,v(p)}&=g_p^{-1} &&(c\in B_p),\\
Q_{c,p}&=s_c-g_p^{-1} &&(c\in B_p),\\
Q_{pL,pR}&=Q_{pR,pL}=d_p.
\end{aligned}
\tag{121.3}
$$

All other off-diagonal rates are zero. Thus compatible conservative
Markov generators exist for every old norm, but none is irreducible
and none has original-edge support. Their unique closed communicating
class is $V$; their unique stationary probability is
$\pi_x=g_x/h$ on $V$, $\pi_c=0$ on $B$.

**Proof.** The old-to-child entries in (120.4) force $a_c\ge0$.
For every beta parent $p$, the old branch tree has a vertex
$x\ne p,v(p)$: its root has two children, so it has at least three
vertices. The $(x,p)$ entry of $A$ is zero. The corresponding
off-diagonal entry of $\mathcal A$ is therefore

$$
b_p=\sum_{c\in B_p}a_c\le0.
\tag{121.4}
$$

Every summand is nonnegative, so all $a_c=0$. Since $K$ is invertible,
$q=0$. This conclusion uses a nonneighbour of each actual beta leaf;
it does not extend to the singleton-beta source.

Now (120.4) reduces to
$\mathcal A=\left(\begin{smallmatrix}A&0\\PA-KP&K\end{smallmatrix}\right)$.
The child-to-child signs require $K_{cd}\le0$ for $c\ne d$.
For $c\in B_p$ and a different beta parent $p'$, distinct old leaves
are not adjacent, so $(PA)_{c,p'}=0$. The child-to-old sign requires

$$
\sum_{d\in B_{p'}}K_{cd}\ge0.
\tag{121.5}
$$

Every summand is nonpositive, and hence every cross-parent block
vanishes. On its own parent column the sign becomes
$\sum_{d\in B_p}K_{cd}\ge A_{pp}=g_p^{-1}$.
A symmetric two-by-two block with nonpositive off-diagonal entry has
precisely the form (121.1), where $s_c$ is its row sum. No remaining
column imposes another condition: the only nonzero old off-parent
entry in that beta row is $A_{p,v(p)}=-g_p^{-1}$.
This proves necessity and the full rate list. Conversely (121.1)
gives these signs directly, and

$$
(z_L,z_R)K_p(z_L,z_R)^{\mathsf T}
=d_p(z_L-z_R)^2+s_{pL}z_L^2+s_{pR}z_R^2>0
\tag{121.6}
$$

for every nonzero pair. Theorem 120.2 then gives (121.2) and all
three exact transport identities, proving sufficiency.

The old states have no exit to $B$ and their original connected tree
has positive rates in both directions. Every child has the forced
exit $c\to v(p)$, so no other closed class exists and every child is
transient. Stationarity on each old edge follows from
$(g_x/h)g_x^{-1}=(g_y/h)g_y^{-1}$. A stationary probability puts no
mass on $B$: summing its stationary equations over the old set leaves
only nonnegative incoming terms, including a strictly positive exit
rate from every child. Connectedness of the old class then makes its
stationary probability unique. Finally $c$ and $v(p)$ are separated
by the two original edges $c-p-v(p)$, so the forced positive rate
violates original-edge support. Old closure and nonempty $B$ violate
irreducibility. $\square$

**Corollary 121.3 (two distinct obstructions after the metric repair).**
On a native branch with births, exact form/norm/same-clock transport
is compatible with conservative Markov evolution precisely as in
(121.1)--(121.3). Adding either irreducibility or original-edge support
to these requirements makes the class empty. In particular, allowing
non-diagonal state metrics repairs (120.2) but does not supply a local
Markov diffusion on the unchanged occurrence tree.

**Proof.** Apply the necessity and sufficiency in Theorem 121.2. The
forced distance-two rate is present even when every $d_p=0$ and
$s_c=g_p^{-1}$, so neither removing sibling jumps nor minimizing row
sums removes this obstruction. $\square$

## 121.99 追加锚（本行以下为增补区）

## 122. The original five-node successor and a two-parent exclusion

**Proposition 122.1 (full five-node matrix witness).** For the original
source $u=\langle\alpha,\beta\rangle$, order old occurrences as
$(\varepsilon,L,R)$ and born children as $(RL,RR)$. Put $G=I_3$,
$q=0$ and $K=I_2$. The actual successor form and compatible state
metric are

$$
L'=\begin{pmatrix}
2&-1&-1&0&0\\-1&1&0&0&0\\-1&0&3&-1&-1\\
0&0&-1&1&0\\0&0&-1&0&1
\end{pmatrix},\qquad
\mathsf M=\begin{pmatrix}
1&0&0&0&0\\0&1&0&0&0\\0&0&3&-1&-1\\
0&0&-1&1&0\\0&0&-1&0&1
\end{pmatrix}.
\tag{122.1}
$$

With $L$ and $P$ from Corollary 119.2, $T=(I_3,P^{\mathsf T})^{\mathsf T}$
satisfies all three identities (120.2), and

$$
\mathcal A=\mathsf M^{-1}L'
=\begin{pmatrix}
2&-1&-1&0&0\\-1&1&0&0&0\\-1&0&1&0&0\\
-1&0&0&1&0\\-1&0&0&0&1
\end{pmatrix}.
\tag{122.2}
$$

The generator $Q=-\mathcal A$ is conservative Markov, is reducible,
and has the two forced transitions $RL\to\varepsilon$ and
$RR\to\varepsilon$, each of rate one. Neither is an edge of the
original successor tree. For an arbitrary fixed old diagonal norm
$\operatorname{diag}(g_\varepsilon,g_L,g_R)$, all compatible Markov
metrics on this same five-node source are exactly (121.2), with the
single block $K_R$ of (121.1); no additional metrics are omitted.

**Proof.** For $f\in\mathbb R^3$ and $y\in\mathbb R^2$,

$$
\begin{pmatrix}f\\y\end{pmatrix}^{\mathsf T}\mathsf M
\begin{pmatrix}f\\y\end{pmatrix}
=f_\varepsilon^2+f_L^2+f_R^2
 +(y_{RL}-f_R)^2+(y_{RR}-f_R)^2.
\tag{122.3}
$$

This proves positive definiteness and $T^{\mathsf T}\mathsf M T=I_3$.
The actual four edges give $L'$ in (122.1), hence the form identity
in (120.1). Direct multiplication gives $\mathsf M\mathcal A=L'$
for the matrix (122.2) and $\mathcal A T=TL$. Its rows sum to zero
and every off-diagonal entry is nonpositive. Its old states are
closed, while both child rows jump directly to $\varepsilon$.
The all-metric assertion for general $G$ is Theorem 121.2 on this
specific original source. $\square$

**Proposition 122.2 (cross-parent coupling cannot repair locality).**
For $u=\langle\beta,\beta\rangle$ there are two old beta parents
$L,R$, with born order $(LL,LR,RL,RR)$. Set $G=I_3$, $q=0$,
$v=(1,0,-1,0)^{\mathsf T}$ and
$K=I_4+\epsilon vv^{\mathsf T}$ for any $\epsilon>0$.
Although $K\succ0$ and (120.3) satisfies all of (120.2), its
$Q_{LL,R}=Q_{RL,L}=-\epsilon$ are negative. In the entire Markov
class for this source, the $L$ and $R$ sibling blocks must instead
be independent, and all four children have a forced rate one to
$\varepsilon$.

**Proof.** The quadratic form of $K$ is
$\|z\|^2+\epsilon(v^{\mathsf T}z)^2>0$ for $z\ne0$.
In $Q_{B,V}=KP-PA$, the $(LL,R)$ entry is the sum of the $LL$
row over the $R$ block, namely $-\epsilon$, since $A_{L,R}=0$.
The other entry is symmetric between the two parents. The complete
necessity and sufficiency, including all four forced rates, follows
from (121.1)--(121.3). $\square$

## 122.99 追加锚（本行以下为增补区）

## 123. Singleton-beta and empty-birth boundaries

**Theorem 123.1 (all singleton-beta metrics and Markov boundaries).**
Let the old source be $\beta$, so $n=1$, $G=(g_0)$ with $g_0>0$,
$L=0$, $P=(1,1)^{\mathsf T}$, and the successor is the three-node
star $\langle\beta,\alpha\rangle$. All compatible metrics are still
(120.3), now with arbitrary $q\in\mathbb R^2$ and symmetric
$K=\left(\begin{smallmatrix}u&w\\w&v\end{smallmatrix}\right)\succ0$.
Write $a=Kq=(a_1,a_2)^{\mathsf T}$ and $t=a_1+a_2$. Such a metric
gives a conservative Markov generator exactly when

$$
a_1,a_2\ge0,\qquad w\le\min(a_1,a_2),\qquad
u+w\ge t,\quad v+w\ge t.
\tag{123.1}
$$

In this case the full rate matrix is

$$
Q=\begin{pmatrix}
-t&a_1&a_2\\
u+w-t&-u+a_1&a_2-w\\
v+w-t&a_1-w&-v+a_2
\end{pmatrix}.
\tag{123.2}
$$

It is irreducible if and only if
$q_1>0$, $q_2>0$ and $q_1+q_2<1$.
It has original-star-edge support if and only if

$$
a_1=a_2=w=c\ge0,\qquad u\ge c,\quad v\ge c,
\qquad uv>c^2,
\tag{123.3}
$$

where positive definiteness also retains $u,v>0$. Within this local
class it is irreducible if and only if $c>0$, $u>c$ and $v>c$.
Thus local irreducible compatible metrics exist at this boundary.

**Proof.** Theorem 120.2 applies also when the old form is zero.
Substituting $P$ into (120.4) gives (123.2), and its six
off-diagonal signs are exactly (123.1). Its zero row sums follow
directly. The successor form has rank two, hence so does
$\mathcal A=\mathsf M^{-1}L'$. A finite conservative Markov matrix
has one independent stationary probability for each closed
communicating class: on each finite closed class existence follows
by taking an accumulation point of Cesaro averages of a row of
$e^{tQ}$, and the maximum principle makes the right kernel on that
class constant; transient classes contribute no stationary mass.
Here the rank gives one closed class. A stationary vector of sum one
is, from (120.3),

$$
g_0^{-1}\mathsf M\mathbf1_3
=(1-q_1-q_2,q_1,q_2)^{\mathsf T},
\qquad \mathbf1_3^{\mathsf T}\mathsf M Q=0.
\tag{123.4}
$$

Indeed $\mathsf M Q=-L'$ and the norm condition gives
$\mathbf1_3^{\mathsf T}\mathsf M\mathbf1_3=g_0$.
The unique stationary probability is strictly positive on every
state exactly when that unique closed class is the whole set. This
proves the irreducibility criterion, including its necessity.
Original-edge support requires both sibling rates $a_2-w$ and
$a_1-w$ to vanish, giving (123.3) with precisely the remaining
Markov signs and positive-definiteness conditions. Its only
off-diagonal rates are $Q_{0i}=c$ and
$Q_{10}=u-c$, $Q_{20}=v-c$, which gives the last criterion.
$\square$

**Proposition 123.2 (explicit local irreducible exceptional metric).**
On the singleton-beta step, put

$$
\mathsf M=g_0\left(I_3-\frac29\mathbf1_3\mathbf1_3^{\mathsf T}\right),
\qquad \mathcal A=g_0^{-1}L',\qquad
L'=\begin{pmatrix}2&-1&-1\\-1&1&0\\-1&0&1\end{pmatrix}.
\tag{123.5}
$$

This metric is positive definite, satisfies (120.2), and its Markov
generator is irreducible with original-star-edge support.

**Proof.** The metric has eigenvalue $g_0/3$ on constants and
$g_0$ on their orthogonal complement. Since $L'$ kills constants,
$\mathsf M^{-1}L'=g_0^{-1}L'$. Here $T=\mathbf1_3$ and
$T^{\mathsf T}\mathsf M T=g_0$, while $L'T=0=TL$.
Both edge directions have rate $g_0^{-1}>0$. Equivalently its
parameters are $q=(1/3,1/3)^{\mathsf T}$ and
$K=g_0^{-1}\left(\begin{smallmatrix}2&1\\1&2\end{smallmatrix}\right)$,
which satisfy the strict local conditions of Theorem 123.1.
$\square$

**Proposition 123.3 (empty births and exhaustive native alternatives).**
If $B=\varnothing$, then $T=I_n$, $L'=L$ and the unique successor
metric satisfying (120.2) is $\mathsf M=G$. Its rate matrix is
$Q=-G^{-1}L$, which is conservative, irreducible and supported on
the original edges; the one-state zero generator is included in
this convention. Every finite native source step falls into exactly
one of the following cases: empty births; the singleton-beta
boundary of Theorem 123.1; or a nontrivial branch with births as in
Theorem 121.2. Consequently a compatible Markov metric always exists.
On a branch it admits irreducibility, or original-edge support, if
and only if births are empty. On the singleton-beta step, each
additional property is characterized by (123.1)--(123.3).

**Proof.** With $T=I_n$, the norm equality forces $\mathsf M=G$;
all other requirements follow. The old tree is connected and all
its edge rates are positive, giving irreducibility. A native source
is either $\alpha$, $\beta$, or a branch, and births occur exactly
at beta leaves. The alpha singleton has no births; the beta
singleton has two; a branch is nontrivial. The classifications and
existence assertions now follow from Theorems 121.2 and 123.1 and
Proposition 123.2. $\square$

## 123.99 追加锚（本行以下为增补区）
