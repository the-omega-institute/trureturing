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

## 124. Finite coherent residual transport on every accepted prefix

The source-indexed occurrence objects, old/new incidence maps and unit-edge
forms are those of IV §§112--113 and VI §§114--115. In particular, an
occurrence address is never quotient-identified, and the parent-copy map is
fixed by the actual birth incidence. The comparison clock and spatial
boundary remain the separately typed objects of III §81. The following
construction uses V Lemma 117.2 only for the already established ancestry
fibres; it does not replace those fibres by a limiting source.

**Definition 124.1 (accepted prefix and residual chart).** Fix an arbitrary
finite source $u\in D$ and a finite accepted history through epochs
$0,1,\ldots,m$. Write

$$
V_e=V_e(u),\quad B_e=B_e(u),\quad P_e=C_e^*,\quad L_e=L_e(u),
\qquad 0\le e<m,
$$

with the old coordinates first at every step. Let
$T_e:\mathbb R^{V_e}\to\mathbb R^{V_{e+1}}$ be
$T_ef=(f,P_ef)$. Define residual coordinates of a final field
$z\in\mathbb R^{V_m}$ recursively by

$$
 x_0=z|_{V_0},\qquad
 y_e=z|_{B_e}-P_ex_e,qquad
 x_{e+1}=(x_e,P_ex_e+y_e),
\tag{124.1}
$$

where the last equality uses the actual old/new ordering of $V_{e+1}$.
The map

$$
\mathcal W_m:\mathbb R^{V_0}\oplus
 \bigoplus_{e=0}^{m-1}\mathbb R^{B_e}\longrightarrow\mathbb R^{V_m},
\qquad
(x_0,y_0,\ldots,y_{m-1})\longmapsto z,
\tag{124.2}
$$

is the inverse of this residualization. Empty birth blocks are zero
summands. Put $T_{0,m}=T_{m-1}\cdots T_0$.

**Lemma 124.2 (simultaneous form diagonalization).** In the coordinates
(124.2),

$$
\mathcal W_m^{\mathsf T}L_m\mathcal W_m
 =\operatorname{diag}\left(L_0,I_{B_0},I_{B_1},\ldots,I_{B_{m-1}}\right),
\qquad
\mathcal W_m^{-1}T_{0,m}x=(x,0,\ldots,0).
\tag{124.3}
$$

For every $e<m$, the prefix chart $\mathcal W_e$ is the restriction of
$\mathcal W_m$ to the first $e$ residual blocks, and the one-step chart from
$V_e$ to $V_{e+1}$ is

$$
\mathsf W_e(f,y)=(f,P_ef+y).
\tag{124.4}
$$

**Proof.** For one step, VI (120.5) gives

$$
\mathsf W_e^{\mathsf T}L_{e+1}\mathsf W_e
 =\operatorname{diag}(L_e,I_{B_e}).
$$

Apply this identity successively to the actual old/new decomposition. The
birth residual at stage $e$ is independent of all earlier residuals, so the
successive congruences give the first identity in (124.3). A parent-copy has
zero residual at its own stage; induction gives the second identity. The
empty-block case is the identity congruence. The same induction proves the
prefix assertion. $\square$

**Theorem 124.3 (finite-stage coherent SPD realization).** Choose an
arbitrary SPD matrix $M_0$ on $\mathbb R^{V_0}$ and, for each nonempty
$B_e$, an arbitrary SPD matrix $K_e$ on $\mathbb R^{B_e}$. Define

$$
\widehat M_m
 =\operatorname{diag}\left(M_0,K_0^{-1},\ldots,K_{m-1}^{-1}\right),
\qquad
M_m=\mathcal W_m^{-\mathsf T}\widehat M_m\mathcal W_m^{-1},
\tag{124.5}
$$

and define $M_e$ by the corresponding prefix of (124.5). Set

$$
A_e=M_e^{-1}L_e.
\tag{124.6}
$$

Then, for every $e<m$,

$$
T_e^{\mathsf T}L_{e+1}T_e=L_e,
\qquad
T_e^{\mathsf T}M_{e+1}T_e=M_e,
\qquad
A_{e+1}T_e=T_eA_e.
\tag{124.7}
$$

Consequently $e^{-tA_{e+1}}T_e=T_ee^{-tA_e}$ for every $t\ge0$, and the
same comparison clock works at every accepted epoch. Every $M_e$ is SPD.
If $B_e\ne\varnothing$, the actual-coordinate matrix $M_{e+1}$ is generally
non-diagonal even when $M_e$ and $K_e$ are diagonal.

**Proof.** The first identity is (124.3) at one stage. In residual
coordinates the metric and generator are

$$
\widehat M_{e+1}=\operatorname{diag}(\widehat M_e,K_e^{-1}),
\qquad
\widehat A_{e+1}=\operatorname{diag}(A_e,K_e).
\tag{124.8}
$$

Thus the inclusion of the old coordinates preserves both the metric and the
generator. Conjugating (124.8) by the invertible map (124.4) gives (124.7).
Positive definiteness is preserved by congruence. The exponential identity is
the finite matrix power-series consequence of the last equation in (124.7).
When $B_e\ne\varnothing$, the off-diagonal actual block is
$-P_e^{\mathsf T}K_e^{-1}$ in the choice with zero residual cross block;
it is nonzero because every newborn has a parent. $\square$

The construction is prefix-wise and does not assert a single infinite
operator or an infinite-dimensional SPD metric. It includes a stopped or
capped history by taking its last finite prefix. At an empty-birth step,
$B_e=\varnothing$, $T_e=I$, $M_{e+1}=M_e$ and $A_{e+1}=A_e$. For the
singleton $α$, the first step is of this form. For the singleton $β$,
$V_0$ has one coordinate and the first nonempty block has two coordinates;
no connectedness or positive old edge form is needed in (124.3). For an
arbitrary initial branch, the same construction starts from its actual
occurrence set and leaves all original coordinates fixed.

## 125. Conservative Markov choices inside the coherent class

**Definition 125.1 (coherent conservative family and occurrence range).** A
coherent family on an uncapped accepted history is a sequence
$(M_e,A_e)_{e\ge0}$ satisfying (124.7) at every accepted step, with each
$M_e$ SPD. It is Markov-compatible when

$$
Q_e=-A_e,\qquad Q_e\mathbf 1=0,qquad Q_e(x,y)\ge0\quad(x\ne y).
\tag{125.1}
$$

Its occurrence-distance jump range is

$$
\operatorname{jr}(Q_e)=\max\{d_e(x,y):x\ne y, Q_e(x,y)>0\},
\tag{125.2}
$$

with value $0$ when there is no positive off-diagonal rate.

**Proposition 125.2 (a Markov extension at every finite stage).** Suppose
$(M_e,Q_e)$ is a coherent Markov prefix and $B_e\ne\varnothing$. For
$p\in M_e$ put

$$
 s_e(p)=-Q_e(p,p)=\sum_{y\ne p}Q_e(p,y),
$$

and choose numbers $\kappa_c>0$ for $c\in B_e$. In Theorem 124.3 take
$q_e=0$ in the residual block and

$$
K_e=\operatorname{diag}(s_e(\operatorname{par}_e(c))+\kappa_c:c\in B_e).
\tag{125.3}
$$

The resulting $Q_{e+1}$ is conservative Markov. Its nonzero off-diagonal
rates are exactly

$$
\begin{aligned}
Q_{e+1}(x,y)&=Q_e(x,y)&& (x,y\in V_e, x\ne y),\\
Q_{e+1}(x,c)&=0&& (x\in V_e, c\in B_e),\\
Q_{e+1}(c,y)&=Q_e(p,y)&& (y\in V_e\setminus\{p\}),\\
Q_{e+1}(c,p)&=\kappa_c,\\
Q_{e+1}(c,d)&=0&& (c\ne d),
\end{aligned}
\tag{125.4}
$$

where $p=\operatorname{par}_e(c)$. Therefore every finite actual history,
including all singleton and empty-birth endpoints, admits a coherent Markov
family; its intermediate state metrics may be non-diagonal.

**Proof.** With zero residual cross block, the one-step version of (124.8)
gives

$$
Q_{e+1}
 =-\begin{pmatrix}Q_e&0\\P_eQ_e-K_eP_e&K_e\end{pmatrix}
\quad\text{in residual coordinates conjugated by }\mathsf W_e.
$$

For a newborn $c$ over $p$, (125.3) gives rate $\kappa_c$ to $p$, rate
$Q_e(p,y)$ to every other old destination $y$, and no sibling rate. All
these rates are nonnegative. The row sum is
$\kappa_c+s_e(p)-[s_e(p)+\kappa_c]=0$; old rows are unchanged. Thus
(125.4) holds and the matrix is conservative Markov. Starting with
$M_0=I$ gives $Q_0=-L_0$, which is Markov on every original tree (and is the
zero generator on either singleton), so induction gives the existence claim.
The endpoint statements follow from the empty-block convention in §124.
$\square$

**Proposition 125.3 (fixed-source long-range witness).** Let
$u=\langle\alpha,\beta\rangle$, take $M_0=I_3$ in the old order
$(\varepsilon,L,R)$, and use (125.3) with every $\kappa_c=1$. Then the
coherent Markov family satisfies, for every $m\ge0$,

$$
Q_m(RL^m,\varepsilon)=1,
\qquad
 d_m(RL^m,\varepsilon)=m+1,
\qquad
\operatorname{jr}(Q_m)\ge m+1.
\tag{125.5}
$$

Here $RL^m$ is an actual occurrence, not a subtree quotient. The transition
at $m=0$ is the old edge $R\to\varepsilon$; for $m\ge1$ it is inherited
through the beta-left lineage and is a non-edge of the current occurrence
tree.

**Proof.** At epoch zero, $Q_0=-L_0$ gives
$Q_0(R,\varepsilon)=1$. The address $R$ is beta, and the left child $RL$ is
beta at epoch one. Formula (125.4) transfers the positive rate from $R$ to
$\varepsilon$ to $RL$ because $\varepsilon$ is not a newborn parent. Inductively,
$RL^m$ is beta at epoch $m$, its left child is $RL^{m+1}$, and the same
rate is transferred. The address length is $m+1$, proving (125.5). $\square$

## 126. The uncapped range boundary

The next statement concerns the universal question, rather than only the
choice (125.3). The finite occurrence geometry used here is the ancestry
geometry of V Lemma 117.2: each original terminal supplies a separate finite
Fibonacci fibre, and the only beta child of a born beta fibre is its left
child.

**Lemma 126.1 (range-bounded residual forcing).** Let a coherent Markov
family have $\operatorname{jr}(Q_e)\le R$ for two successive epochs, and
suppose every beta leaf $p\in M_e$ has some old occurrence at distance $>R$.
Then the residual cross vector in the general one-step chart is zero:
$q_e=0$ (equivalently $a_e=K_eq_e=0$).

**Proof.** In the general residual chart, write $a_e=K_eq_e$ and
$b_e=P_e^{\mathsf T}a_e$. The old-to-new rates are
$Q_{e+1}(x,c)=a_e(c)\ge0$, and the old-old off-diagonal rates are
$Q_e(x,y)-b_e(y)$. For a beta leaf $y$, choose $x$ with
$d_e(x,y)>R$. The range assumption gives $Q_e(x,y)=0$ and
$Q_{e+1}(x,y)\ge0$, hence $b_e(y)\le0$. But
$b_e(y)=\sum_{c\in B_y}a_e(c)\ge0$, so it is zero, and all the two terms in
that sum are zero. This holds for every beta leaf, hence $a_e=0$; $K_e$ is
invertible, so $q_e=0$. $\square$

**Lemma 126.2 (FIB frontier escape).** Consider an uncapped accepted
iteration from any epoch whose current source has at least two terminal leaf
cones. Let
$(Q_e)$ be coherent and conservative Markov. If its ranges were bounded by a
single $R$, then, after a finite initial prefix, the beta-leaf rows would
have to be closed inside the beta-leaf set at every epoch. This is impossible.

**Proof.** By the separate terminal fibres and their ancestry distances, for
all sufficiently large $e$ every beta leaf has a vertex at distance $>R$;
Lemma 126.1 therefore gives $q_e=0$. In that case the $q_e=0$ block gives the deterministic-fibre identity

$$
\sum_{z:\,\pi_e(z)=y}Q_{e+1}(x,z)=Q_e(\pi_e(x),y),
\tag{126.1}
$$

where $\pi_e$ fixes old vertices and sends a newborn to its beta parent.
The rank identity
$\operatorname{rank}Q_e=|V_e|-1$ follows from
$\operatorname{rank}L_e=|V_e|-1$ and invertibility of $M_e$. A finite
conservative Markov matrix of this rank has exactly one closed communicating
class.

Suppose a beta leaf $p\in M_e$ has a positive rate to
$y\notin M_e$. Let $p_j=pL^j$, which is a beta leaf at epoch $e+j$. Iterating
(126.1) gives

$$
\sum_{z:\,\pi_{e,e+j}(z)=y}Q_{e+j}(p_j,z)=Q_e(p,y)>0.
\tag{126.2}
$$

The target fibre on the left lies below the old occurrence $y$, while $p_j$
lies $j$ edges below $p$. Since $p$ and $y$ are distinct occurrences, every
term with a positive rate has

$$
d_{e+j}(p_j,z)\ge d_e(p,y)+j.
\tag{126.3}
$$

This covers both possibilities for $y\notin M_e$: a branch occurrence is
permanent, and an alpha occurrence is promoted before it can acquire its own
children; in either case all points of its later parent fibre remain below
$y$. Equations (126.2)--(126.3) contradict a uniform range bound as
$j\to\infty$.

It remains to consider the alternative that every beta row stays inside the
beta set. The beta set is then a nonempty closed set. Its old vertices become
branch vertices at the next accepted step, while their beta left children
are new beta leaves. If all those new beta rows also stayed inside their new
beta set, that set would be a closed set disjoint from the old beta closed
class. This contradicts the one-closed-class consequence of the rank
identity. Hence a beta row leaves at some later epoch, reducing to the first
case. The contradiction proves the lemma. $\square$

**Theorem 126.3 (no single finite range on uncapped coherent Markov transport).**
For every coherent compatible conservative Markov family on an uncapped FIB
iteration that reaches a branch epoch,

$$
\sup_{e\ge0}\operatorname{jr}(Q_e)=+\infty.
\tag{126.2}
$$

The conclusion is universal over the family; it does not depend on the
particular Markov choice (125.3). A finite stopped or capped history has a
finite maximum range because it has finitely many epochs. The singleton
sources are included after their first nonempty branch epoch: $\alpha$ first
has the empty-birth step, $\beta$ first has the two-child step. Thus the
statement does not assert a bound for a history that stops before that
branch is accepted.

**Proof.** If (126.2) failed, a finite $R$ would bound all epochs. At the first branch
epoch the current source has two terminal leaf cones, and each singleton
reaches such an epoch after finitely many accepted steps. Lemma 126.2
contradicts that bound.
Empty births and refused or stopped suffixes contribute no additional epoch
and are covered by the finite-prefix statement. $\square$

The first repaired successor can therefore leave the narrower old diagonal
class while retaining exact finite coherence. Theorem 121.2 remains a
conditional statement for a diagonal old norm at one branch step; it is not a
classification of the matrices $M_e$ in (124.5). Markov positivity in
(125.1), irreducibility, original-edge support, occurrence-distance range,
fixed-form realization, finite-stage coherence, and an infinite-process
realization are distinct properties. The construction above supplies the
first, fixed-form finite coherence, and the explicit range witness; it does
not supply irreducibility or original-edge support at all branch epochs, and
it does not install a physical spatial geometry or an infinite-dimensional
operator.

No new literature theorem is used in §§124--126. The only external matrix
fact already cited in VI §120 is the SPD Schur-complement identity; the
remaining steps are finite congruence, Markov sign, rank, and the accepted
FIB ancestry relations. The all-state physical locality added in DEV
753b783b035 concerns finite-difference annihilation of corrected-field
commutators and has no occurrence-distance generator-range assertion.

## 126.99 追加锚（本行以下为增补区）

## 127. Full-source residual metrics with an arbitrary inherited norm

**Definition 127.1 (source, metric and reference conventions).** Throughout
§§127--130 the source quantifier is the full finite algebra

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle v,w\rangle=\langle\rho v,\rho w\rangle.
\tag{127.1}
$$

For every $u\in\mathcal T$, an actual history with $m$ accepted updates has
current source $s_e=\rho^e u$ at each accepted epoch $0\le e\le m$.
Reads and refused attempts do not advance $e$. An accepted update with no
new occurrences does advance $e$, because it changes the terminal labels.
Stopping or a cap selects a finite accepted prefix; it does not remove an
accepted empty-birth step from that prefix. For an uncapped iteration all
accepted epochs $e\in\mathbb N$ are available. The semigroup parameter
$t\ge0$ is separate from $e$ and is the same parameter on both sides of
each intertwining identity.

Use the actual occurrence vertices $V_e$, their original unit edges $E_e$,
and $L_e$ of IV Definition 92.1. Set
$\mathcal P_e=\{p\in V_e:s_e|_p=\beta\}$ and
$B_e=\{pL,pR:p\in\mathcal P_e\}$.
Write $G_e\succ0$ for the state metric and $A_e=G_e^{-1}L_e$,
$Q_e=-A_e$. Thus $G_e$ is the metric denoted $M_e$ in §124, whereas
$\mathcal P_e$ is the beta-parent set denoted $M_e$ in IV (112.6).
These two objects have different types. For the entire $\mathcal T$,
including both singleton sources, define $P_e$ and $T_e$ by
$(P_ef)(c)=f(\operatorname{par}_e(c))$ and $T_ef=(f,P_ef)$.
The old coordinates and edges retain their literal addresses. No port
triple is required at a singleton.

These conventions replace the branch-only source quantifier of Definition
124.1 for the statements below. Proposition 127.2 supplies the previously
unspecified residual cross vector used in Lemma 126.1, and Proposition
128.2 replaces the signed block display in the proof of Proposition 125.2.
Theorem 129.3 replaces the proof and source scope of Theorem 126.3, using
Proposition 128.3 for the accepted empty steps and first usable branch
epochs. The two distinct displays bearing the old tag
(126.2) are distinguished as the fibre-sum display in Lemma 126.2 and the
range display in Theorem 126.3; their unambiguous replacements are (129.5)
and (129.3), respectively. The finite residual construction of §124 and
the fixed-source witness of Proposition 125.3 retain their conclusions.

**Proposition 127.2 (one-step cross block for a general old SPD metric).**
Fix any $u\in\mathcal T$ and any actual accepted step $e\to e+1$.
Abbreviate $n=|V_e|$, $k=|B_e|$, $G=G_e\succ0$, $L=L_e$,
$A=G^{-1}L$, $Q=-A$, and $P=P_e$. The old metric $G$ is an arbitrary
real symmetric positive-definite matrix, with no diagonal or entrywise-sign
restriction. In actual and residual coordinates, respectively, put

$$
\begin{aligned}
L_+&=\begin{pmatrix}L+P^{\mathsf T}P&-P^{\mathsf T}\\-P&I_k\end{pmatrix},
&T&=\begin{pmatrix}I_n\\P\end{pmatrix},\\
W&=\begin{pmatrix}I_n&0\\P&I_k\end{pmatrix},
&W^{-1}&=\begin{pmatrix}I_n&0\\-P&I_k\end{pmatrix},\\
W^{\mathsf T}L_+W&=\operatorname{diag}(L,I_k),
&W^{-1}T&=\begin{pmatrix}I_n\\0\end{pmatrix}.
\end{aligned}
\tag{127.2}
$$

If $k>0$, the compatible successor metrics are exactly the following,
parameterized uniquely by $q$ and $K$:

$$
\begin{aligned}
g&=G\mathbf1_n,\qquad h=\mathbf1_n^{\mathsf T}G\mathbf1_n>0,\\
H&=W^{\mathsf T}G_+W
 =\begin{pmatrix}
 G&gq^{\mathsf T}\\qg^{\mathsf T}&K^{-1}+hqq^{\mathsf T}
 \end{pmatrix},
\qquad G_+=W^{-\mathsf T}HW^{-1},
\qquad q\in\mathbb R^k,\quad K=K^{\mathsf T}\succ0.
\end{aligned}
\tag{127.3}
$$

Here compatible means $T^{\mathsf T}G_+T=G$ and
$G_+^{-1}L_+T=TA$. In particular the one-step parameters $q_e$ and
$K_e$ are defined by (127.3), using the actual inherited $G_e$, not a
diagonal replacement. This parameterization does not impose Markov signs.
For $k=0$ the unique compatible successor is $G_+=G$ and $Q_+=Q$;
there is no cross vector to choose.

**Proof.** The unit-edge birth relation gives (127.2) directly. Norm
preservation fixes the upper-left block of $H$ to be $G$. Write
$H=\left(\begin{smallmatrix}G&X\\X^{\mathsf T}&Z\end{smallmatrix}\right)$.
Multiplying generator intertwining in residual coordinates by $H$ gives

$$
H\begin{pmatrix}G^{-1}L\\0\end{pmatrix}
 =\begin{pmatrix}L\\0\end{pmatrix},
\qquad X^{\mathsf T}G^{-1}L=0.
\tag{127.4}
$$

The occurrence tree is connected, including the one-vertex tree. Its
edge-energy identity implies $\ker L=\mathbb R\mathbf1_n$.
Each row of $X^{\mathsf T}G^{-1}$ is therefore a unique scalar multiple
of $\mathbf1_n^{\mathsf T}$. Collect those scalars in $q$, obtaining
$X^{\mathsf T}G^{-1}=q\mathbf1_n^{\mathsf T}$, or
$X=gq^{\mathsf T}$. For $n=1$, $L=0$ and this conclusion still describes
every possible one-column $X^{\mathsf T}$, since $G>0$.

As $G^{-1}g=\mathbf1_n$, the Schur complement of $G$ is
$Z-hqq^{\mathsf T}$. Positive definiteness of $H$ is equivalent to
this complement being positive definite; write it uniquely as $K^{-1}$.
This is the same Schur-complement identity cited in §120, applied now
without a diagonal hypothesis on $G$. It proves necessity, sufficiency
and uniqueness of (127.3). The inverse is explicitly

$$
H^{-1}=\begin{pmatrix}
G^{-1}+\mathbf1_n(q^{\mathsf T}Kq)\mathbf1_n^{\mathsf T}
 &-\mathbf1_n q^{\mathsf T}K\\
-Kq\mathbf1_n^{\mathsf T}&K
\end{pmatrix}.
\tag{127.5}
$$

Multiplication by $\operatorname{diag}(L,I_k)$ verifies (127.4) and the
generator identities below. If $k=0$, $T=I_n$ and norm preservation
already forces $G_+=G$. $\square$

**Corollary 127.3 (signed residual-to-actual generator identity).** In the
nonempty-birth case of Proposition 127.2, define $a=Kq$, $b=P^{\mathsf T}a$ and
$D_K=K-\mathbf1_k a^{\mathsf T}$. Then the residual generators are

$$
\begin{aligned}
\widetilde A_+&=W^{-1}(G_+^{-1}L_+)W
 =H^{-1}\operatorname{diag}(L,I_k)
 =\begin{pmatrix}A&-\mathbf1_n a^{\mathsf T}\\0&K\end{pmatrix},\\
\widetilde Q_+&=-\widetilde A_+
 =\begin{pmatrix}Q&\mathbf1_n a^{\mathsf T}\\0&-K\end{pmatrix}.
\end{aligned}
\tag{127.6}
$$

Their actual-coordinate relation is the conjugation identity

$$
\begin{aligned}
Q_+&=W\widetilde Q_+W^{-1}
 =\begin{pmatrix}
 Q-\mathbf1_n b^{\mathsf T}&\mathbf1_n a^{\mathsf T}\\
 PQ+D_KP&-D_K
 \end{pmatrix},\\
A_+&=W\widetilde A_+W^{-1}=-Q_+,
\qquad Q_+\mathbf1_{n+k}=0.
\end{aligned}
\tag{127.7}
$$

**Proof.** In (127.5), $\mathbf1_n^{\mathsf T}L=0$ removes both the
rank-one correction in the upper-left block and the lower-left block of
the product with the residual form. This gives (127.6). Multiplying its
second matrix first on the right by $W^{-1}$ gives upper blocks
$Q-\mathbf1_n a^{\mathsf T}P$, $\mathbf1_n a^{\mathsf T}$ and lower
blocks $KP$, $-K$. Multiplication on the left by $W$, using
$P\mathbf1_n=\mathbf1_k$, gives exactly (127.7). Moreover
$Q\mathbf1_n=0$ and
$b^{\mathsf T}\mathbf1_n=a^{\mathsf T}\mathbf1_k$, so its upper row
sums vanish; the lower row sums are
$PQ\mathbf1_n+D_KP\mathbf1_n-D_K\mathbf1_k=0$.
Thus conservation holds even before Markov positivity is imposed.
No entrywise property of $G$ was used. $\square$

## 128. Finite coherence, consistent Markov rates and the initial epochs

**Theorem 128.1 (full-source finite realization).** For every
$u\in\mathcal T$, every finite actual history with $m\ge0$ accepted
updates, every SPD initial metric $G_0$ on $\mathbb R^{V_0(u)}$, and every
choice of SPD $K_e$ on each nonempty $B_e$, the native parent-copy maps
admit SPD metrics through all epochs $0,\ldots,m$ satisfying exact form
and norm preservation and full same-clock generator intertwining.
This includes arbitrary initial branches, $u=\alpha$, $u=\beta$,
empty births, and prefixes stopped or capped at any finite epoch.

**Proof.** Let $\mathcal W_m$ be the reconstruction map of (124.2), now
with the source quantifier of Definition 127.1. Its residual at stage $e$
is the actual child value minus its parent's value. It is invertible by
successive reconstruction at each finite step, and (127.2) inductively
gives (124.3) for every $u\in\mathcal T$. Define

$$
G_m=\mathcal W_m^{-\mathsf T}
 \operatorname{diag}(G_0,K_0^{-1},\ldots,K_{m-1}^{-1})
 \mathcal W_m^{-1},
\tag{128.1}
$$

with each empty block omitted, and use the corresponding prefixes for
$G_e$. Equivalently at each single step,
$W_e^{\mathsf T}G_{e+1}W_e=\operatorname{diag}(G_e,K_e^{-1})$.
This is the $q_e=0$ case of (127.3), with the inherited actual-coordinate
$G_e$; it is not a claim that $G_e$ is diagonal. Hence, for every $e<m$,

$$
\begin{aligned}
T_e^{\mathsf T}L_{e+1}T_e&=L_e,&
T_e^{\mathsf T}G_{e+1}T_e&=G_e,\\
A_{e+1}T_e&=T_eA_e,&
e^{-tA_{e+1}}T_e&=T_ee^{-tA_e}\quad(t\ge0).
\end{aligned}
\tag{128.2}
$$

The last equality follows term by term from the finite matrix exponential
series. Each metric is SPD by congruence. For $m=0$ there is no extension
condition. For $B_e=\varnothing$ the chart is the identity and
$G_{e+1}=G_e$, $A_{e+1}=A_e$. These observations also cover a final
accepted empty step. No future epoch is required for a finite prefix.
$\square$

**Proposition 128.2 (correct Markov extension with inherited metrics).**
For every $u\in\mathcal T$ and every coherent finite prefix for which
$Q_e=-G_e^{-1}L_e$ is conservative Markov, a further accepted step has a
coherent conservative Markov extension. The inherited $G_e$ may be
non-diagonal. For a nonempty birth block set
$s_e(p)=-Q_e(p,p)=\sum_{y\ne p}Q_e(p,y)$, choose
$\kappa_c>0$ for each child, and take
$q_e=0$ and $K_e=\operatorname{diag}(s_e(\operatorname{par}_e(c))+
\kappa_c:c\in B_e)$ in (127.3).

**Proof.** Each diagonal entry of $K_e$ is positive. Writing $P=P_e$,
$K=K_e$, $W=W_e$ for this step, the signed residual and actual matrices
are

$$
\widetilde Q_{e+1}=\begin{pmatrix}Q_e&0\\0&-K\end{pmatrix},
\qquad
Q_{e+1}=W\widetilde Q_{e+1}W^{-1}
 =\begin{pmatrix}Q_e&0\\PQ_e+KP&-K\end{pmatrix}.
\tag{128.3}
$$

Thus there is no overall minus sign outside a block whose old block is
already $Q_e$. In particular, in the original occurrence coordinates,
for $c\in B_e$ over $p=\operatorname{par}_e(c)$,

$$
\begin{aligned}
Q_{e+1}(x,y)&=Q_e(x,y)&& (x,y\in V_e),\\
Q_{e+1}(x,c)&=0&& (x\in V_e),\\
Q_{e+1}(c,y)&=Q_e(p,y)&& (y\in V_e\setminus\{p\}),\\
Q_{e+1}(c,p)&=-s_e(p)+[s_e(p)+\kappa_c]=\kappa_c,\\
Q_{e+1}(c,d)&=0&& (d\in B_e\setminus\{c\}),\\
Q_{e+1}(c,c)&=-s_e(p)-\kappa_c.
\end{aligned}
\tag{128.4}
$$

All off-diagonal entries are nonnegative. An old row has its old zero
sum, and a child row has sum
$s_e(p)+\kappa_c-[s_e(p)+\kappa_c]=0$. Equation (128.3) is the actual
conjugation proving these signs and rates, replacing the inconsistent
display in the proof of Proposition 125.2. At an empty step use the unique
extension $G_{e+1}=G_e$, $Q_{e+1}=Q_e$. Starting at $G_0=I$ gives
$Q_0=-L_0$, which is conservative Markov on every source tree, including
the zero generator on either singleton. Induction proves full-source
Markov existence through every finite accepted prefix. More generally
any initial SPD metric whose $-G_0^{-1}L_0$ is Markov admits this extension;
an arbitrary SPD initial metric is guaranteed exact coherence by Theorem
128.1 but is not thereby guaranteed Markov positivity. $\square$

**Proposition 128.3 (empty initial steps and the first usable branch epoch).**
For every $u\in\mathcal T$ the empty-birth steps have exactly
$\mathcal P_e=B_e=\varnothing$, $V_{e+1}=V_e$, $L_{e+1}=L_e$,
$T_e=I$ and $G_{e+1}=G_e$ for every compatible metric. Every terminal
at such a step is alpha and becomes beta. In an uncapped iteration put

$$
h(u)=\min\{e\ge0:s_e\text{ is a branch and }\mathcal P_e\ne\varnothing\}.
\tag{128.5}
$$

This epoch always exists. It is $0$ for a branch with a beta leaf, $1$
for an all-alpha branch, $1$ for $u=\beta$, and $2$ for $u=\alpha$.
At epoch $h(u)$ there are at least two distinct terminal leaf cones and
a nonempty birth set. Every later epoch also has beta leaves.

**Proof.** No beta leaf means no born children. The actual substitution
in (127.1) then preserves all occurrences and changes every terminal
label from alpha to beta, so the step is accepted and advances the epoch
despite its identity matrices. For an all-alpha branch this is the step
$0\to1$, after which the unchanged branch has beta leaves and its first
nonempty births occur at $1\to2$. For the alpha singleton, the step
$0\to1$ gives the beta singleton with its one old coordinate, zero form
and unchanged positive scalar metric. Its first nonempty birth is
$1\to2$, producing $\langle\beta,\alpha\rangle$ at epoch $2$.
For the beta singleton the first nonempty birth is already $0\to1$,
and the same branch is present at epoch $1$. Both singleton birth
incidences are $P=(1,1)^{\mathsf T}$ with $T=\mathbf1_3$; Proposition
127.2 includes any compatible parameters at this step, not only $q=0$.
An arbitrary branch with a beta leaf has the required two leaf cones at
epoch $0$. Finally a beta leaf always produces a beta left child, so
nonemptiness persists after $h(u)$. A stopped history need not reach
$h(u)$ and needs only the finite theorem. $\square$

## 129. Universal range forcing and frontier escape

**Lemma 129.1 (range forcing without a diagonal-old hypothesis).** Fix any
$u\in\mathcal T$ and a compatible conservative Markov step with
$B_e\ne\varnothing$. Its old and successor metrics may be arbitrary
SPD matrices satisfying (128.2), including any inherited non-diagonal
ones. Suppose $\operatorname{jr}(Q_e)\le R$ and every
$p\in\mathcal P_e$ has an $x\in V_e$ with $d_e(x,p)>R$.
Then the uniquely defined cross vector of (127.3) is $q_e=0$.
In particular this holds under the two-epoch range bound in Lemma 126.1;
no successor range bound beyond its Markov signs is needed here.

**Proof.** From (127.7), with $a_e=K_eq_e$ and
$b_e=P_e^{\mathsf T}a_e$,

$$
Q_{e+1}(x,c)=a_e(c)\ge0,\qquad
Q_{e+1}(x,p)=Q_e(x,p)-b_e(p)\quad(x\ne p),\qquad
b_e(p)=\sum_{c:\operatorname{par}_e(c)=p}a_e(c).
\tag{129.1}
$$

The old-to-child entry is off-diagonal for every old $x$, hence every
$a_e(c)$ is nonnegative. For the specified distant $x$, the old range
bound gives $Q_e(x,p)=0$ and the successor Markov sign gives
$b_e(p)\le0$. Its two summands in (129.1) are nonnegative, so both
vanish. This applies to every actual beta parent, accounting for every
child, and therefore $a_e=0$. Since $K_e$ is invertible, $q_e=0$.
No rate formula for a diagonal old metric enters this argument. $\square$

**Lemma 129.2 (deterministic-fibre identity and its source indices).**
For every $u\in\mathcal T$ and every compatible step, let
$\pi_e:V_{e+1}\to V_e$ fix old vertices and send each child to its actual
parent. Then, for all $x\in V_{e+1}$ and $y\in V_e$,

$$
\sum_{z:\pi_e(z)=y}Q_{e+1}(x,z)=Q_e(\pi_e(x),y).
\tag{129.2}
$$

This identity holds also for nonzero $q_e$ and for empty births. For
$j\ge0$ write
$\pi_{e,e+j}=\pi_e\circ\cdots\circ\pi_{e+j-1}$, with the identity for
$j=0$. Iterating (129.2) gives the corresponding identity over each
composite fibre.

**Proof.** The matrix of $T_e$ has entry
$T_e(z,y)=\mathbf1_{\{\pi_e(z)=y\}}$. Therefore the $(x,y)$ entry of
$Q_{e+1}T_e=T_eQ_e$, which is exactly signed generator intertwining,
is (129.2). Applying this to the product of the successive $T_e$ gives
the composite identity; the product is the pullback along
$\pi_{e,e+j}$. This derives the fibre formula directly, rather than
assuming a probabilistic interpretation of the chart. $\square$

**Theorem 129.3 (full-source universal uncapped obstruction).** For every
initial source $u\in\mathcal T$, including every initial branch and
both $\alpha$ and $\beta$, let $(G_e)_{e\ge0}$ be any sequence of
finite SPD metrics on the uncapped actual iteration $s_e=\rho^e u$.
Suppose that at every accepted step the unchanged native unit-edge forms
and parent-copy maps satisfy (128.2), with $A_e=G_e^{-1}L_e$, and that
every $Q_e=-A_e$ is conservative Markov. No diagonality is imposed on
any metric, and the residual parameters may vary arbitrarily subject to
these hypotheses. Then

$$
\sup_{e\ge0}\operatorname{jr}(Q_e)=+\infty.
\tag{129.3}
$$

For every finite stopped or capped history on any $u\in\mathcal T$,
the coherent realizations of Theorem 128.1 and Proposition 128.2 apply
through its last accepted epoch, and the maximum of its finitely many
finite ranges is finite. The uncapped conclusion quantifies over all
coherent Markov families, not only the construction $q_e=0$ or the source
of Proposition 125.3.

**Proof.** Suppose an integer $R\ge0$ bounds all the ranges; an arbitrary
finite real bound can be replaced by its ceiling. Begin the nonempty-birth
argument at $h=h(u)$ of Proposition 128.3. At that epoch fix its entire
terminal antichain $\mathcal L_h$, which has at least two leaves. Each
later leaf is below exactly one $\ell\in\mathcal L_h$. Over two
accepted updates a beta terminal is replaced by descendants at least one
edge deeper, and an alpha terminal first becomes beta and then acquires
two children. Consequently every terminal $p$ at epoch $e\ge h$ has

$$
d_e(p,\ell)\ge\left\lfloor\frac{e-h}{2}\right\rfloor
\quad\text{for its unique ancestor }\ell\in\mathcal L_h.
\tag{129.4}
$$

Indeed the assertion holds at offsets $0$ and $1$, and applying the
two-update observation to every terminal proves it by induction in pairs
of updates. Distinct original terminal cones remain separate, by the
actual address substitution. Choose another $\ell'\in\mathcal L_h$.
It remains an old occurrence, and the unique tree path from $p$ to
$\ell'$ passes through $\ell$, so
$d_e(p,\ell')=d_e(p,\ell)+d_h(\ell,\ell')>R$ whenever
$e\ge h+2(R+1)$. This holds simultaneously for every beta leaf.
Lemma 129.1 therefore forces $q_e=0$ for every step starting at
$e\ge E:=h+2(R+1)$. Formula (127.7) now says that all old rates are
unchanged and no old state has a rate to a newborn. This is a consequence
of the supposed range bound on a tail, not a restriction on the original
family or its finite initial steps.

At every finite epoch, connectedness and the unit-edge energy identity
give $\ker L_e=\mathbb R\mathbf1$. Invertibility of $G_e$ then gives
$\operatorname{rank}Q_e=|V_e|-1$, so its left nullity is one. Here is
the finite Markov consequence needed below. The directed graph of
positive off-diagonal rates has a terminal strongly connected component,
hence at least one closed communicating class. On each such class $C$,
choose $r>\max_{x\in C}(-Q_e(x,x))$. The matrix
$S_C=I+Q_e|_C/r$ is stochastic. The Cesaro averages
$m^{-1}\sum_{i=0}^{m-1}\delta_x S_C^i$ have an accumulation point
$\mu_C$ in the finite probability simplex. Their difference after
right multiplication by $S_C$ is
$(\delta_xS_C^m-\delta_x)/m$, which tends to zero. Thus
$\mu_CQ_e|_C=0$. Extended by zero, it is a nonzero left null vector
of $Q_e$, since $C$ is closed. Different closed classes give linearly
independent such vectors by their disjoint supports. Left nullity one
therefore gives exactly one closed class. In particular two disjoint
nonempty closed sets are impossible, because each contains a terminal
communicating class of its finite induced graph.

Fix an epoch $e\ge E$. Suppose a beta leaf $p\in\mathcal P_e$ has a
positive rate to $y\notin\mathcal P_e$. The actual beta-left lineage
$p_j=pL^j$ is a beta leaf at epoch $e+j$ and has composite image $p$.
Lemma 129.2 gives, for every integer $j\ge0$,

$$
\sum_{z:\pi_{e,e+j}(z)=y}Q_{e+j}(p_j,z)=Q_e(p,y)>0.
\tag{129.5}
$$

Every summand is off-diagonal: the composite image of $p_j$ is $p\ne y$.
Thus some such $z$ has a positive rate. If $y$ is an old branch occurrence,
its composite fibre is the singleton $\{y\}$, since it can never again
be a beta leaf. If $y$ is an alpha leaf, it is distinct from the leaf $p$,
and its entire later fibre lies in its own descendant cone, separated from
the descendant cone of $p$. These exhaust $y\notin\mathcal P_e$.
In the first case appending $L^j$ to $p$ adds $j$ edges to the path to
$y$; in the second the path also includes the descent below $y$. Hence
every target in (129.5) satisfies

$$
d_{e+j}(p_j,z)\ge d_e(p,y)+j.
\tag{129.6}
$$

For sufficiently large $j$ a positive summand contradicts the range bound.
Thus at every $e\ge E$ all beta rows must stay inside
$\mathcal P_e$, which is nonempty by Proposition 128.3. The set
$\mathcal P_e$ is therefore closed. Since $q_e=0$, its old rows are
unchanged at epoch $e+1$ and have no exits to newborns, so this same set
of old occurrences remains a nonempty closed set for $Q_{e+1}$.
All its elements become branch occurrences at that step. Accordingly it
is disjoint from $\mathcal P_{e+1}$, which consists of the new beta left
children and the old alpha leaves promoted to beta. The latter set is
also nonempty and closed, by the same conclusion at epoch $e+1$.
This gives two disjoint nonempty closed sets for $Q_{e+1}$, contradicting
the rank/nullity consequence just proved. The uniform bound cannot exist.

The finite-prefix assertion uses no such arbitrarily long lineage: each
$V_e$ is finite and there are only finitely many accepted epochs. In
particular a history stopping before $h(u)$ still includes every accepted
empty step it actually took, and is covered by Theorem 128.1. $\square$

## 130. Source correspondence and applicability of the corrected statements

**Definition 130.1 (mathematical correspondence and boundaries).** The
source algebra and accepted substitution in (127.1) are exactly IV
Definitions 92.1 and 112.1. The branch access fibre $D=\mathcal B$ in
IV (112.1) remains a branch fibre; the full-source quantifier here does
not reinterpret a singleton as producing that branch entry record.
The occurrence sets, old-address inclusions, beta parents and child
incidence are the objects of IV (112.5)--(112.9), extended directly by
the same algebraic definitions to singleton sources. In particular
$P_e=C_e^*$, $P_e^{\mathsf T}P_e=2\operatorname{diag}
(\mathbf1_{\mathcal P_e})$, and the $L_+$ of (127.2) is the unchanged
native unit-edge form. The ancestry fibres in Lemma 129.2 are the actual
fibres described in V Lemma 117.2: an old internal occurrence has a
singleton fibre, and an old leaf has its own substituted finite tree.
They are not quotients by equal subtree values.

Theorems 128.1 and 129.3 compare all signed old fields, every successor
coordinate, exact forms and SPD norms, and the same finite semigroup
parameter $t$. Proposition 128.2 proves conservative Markov existence
on these finite stages; Proposition 125.3 retains its exact rate-one
fixed-source witness because (128.4) is its claimed rate recurrence.
Theorem 129.3 additionally rules out a uniform finite occurrence-distance
jump range for every uncapped compatible conservative Markov family,
including ones that use nonzero cross vectors before range forcing
applies. Theorems 121.2 and Corollary 121.3 retain their diagonal-old
hypothesis from Definition 120.1; they supply a conditional one-step
boundary and are not used to classify arbitrary inherited metrics.

The Schur-complement and inverse identities used in Proposition 127.2
are the standard ingredients cited in VI §120, Boyd--Vandenberghe,
*Convex Optimization*, Appendix A.5.5. The remaining native conclusions
are derived above from the specified incidence, congruence, intertwining
and ancestry relations; no claim of literature novelty is attached to
the finite matrix or Markov facts used inside those derivations.

These statements concern finite occurrence-state spaces and their
specified algebraic comparisons. They do not select a physical spatial
dimension, turn occurrence distance into physical locality, or identify
either the accepted epoch $e$ or semigroup parameter $t$ with a physical
clock. In particular a three-port root compression is not a derivation
of three physical dimensions. They assert neither an infinite-dimensional
operator realization nor all-epoch irreducibility or original-edge
support of the coherent generators. The finite SPD construction and
the universal range obstruction leave those additional realization
questions separate. The arguments here are mathematical prose and carry
no Lean kernel-verification assertion.

## 130.99 追加锚（本行以下为增补区）

## 131. Occurrence support and a physical realization interface

For an accepted epoch $e$, write

$$
A_e:=\{(x,y)\in V_e\times V_e:x\ne y\ \text{and}\ Q_e(x,y)>0\}.
\tag{131.1}
$$

Thus $A_e$ is the positive off-diagonal support of the generator. A
physical realization interface at epoch $e$ consists of a set $X_e$, a
nonnegative distance function $\rho_e$ on $X_e$, and a map
$\iota_e:V_e\to X_e$:

$$
(V_e,d_e,Q_e)\longmapsto (X_e,\rho_e,\iota_e).
\tag{131.2}
$$

The statement below uses the following explicit interpretation. Positive
entries of $Q_e$ are being read as direct physical transitions, and a
**direct-generator locality radius** $0\le\ell<\infty$ means

$$
(x,y)\in A_e\quad\Longrightarrow\quad
\rho_e(\iota_e(x),\iota_e(y))\le \ell.
\tag{131.3}
$$

This is a realization assumption, not a consequence of the occurrence
algebra. If $Q_e$ is an effective generator obtained after eliminating
microscopic variables, (131.3) concerns the effective transitions only;
the theorem below then says nothing about microscopic locality.

## 132. The minimal bounded-preimage bridge

**Theorem 132.1 (bounded-preimage obstruction to direct physical locality).**
Fix one uncapped full-source compatible conservative Markov family from
Theorem 129.3. Suppose a realization interface (131.2) and one finite
radius $0\le\ell<\infty$ satisfy direct-generator locality (131.3) for
every accepted epoch $e$. Assume in addition the minimal bounded-preimage
condition at that radius: there is one finite $R\ge0$, independent of $e$,
such that

$$
(x,y)\in A_e\ \text{and}\
\rho_e(\iota_e(x),\iota_e(y))\le\ell
\quad\Longrightarrow\quad d_e(x,y)\le R
\tag{132.1}
$$

for every accepted epoch $e$. Then

$$
\operatorname{jr}(Q_e)\le R\qquad\text{for every }e,
\tag{132.2}
$$

which contradicts the uncapped universal conclusion
$\sup_e\operatorname{jr}(Q_e)=+\infty$ in Theorem 129.3.

**Proof.** Take any $(x,y)\in A_e$. By (131.3) its physical distance is at
most $\ell$, so (132.1) gives $d_e(x,y)\le R$. The occurrence jump range is
the supremum of these $d_e(x,y)$ over $A_e$, hence (132.2). Theorem 129.3
rules out this uniform finite bound for the fixed uncapped family. The
contradiction uses no claim about a physical dimension or about a
microscopic realization. $\square$

The bounded-preimage clause is the smallest comparison condition used here:
it controls only active pairs inside the declared physical locality radius.
It does not require a correspondence for inactive pairs, a global
quasi-isometry, or an upper control on $\rho_e$.

## 133. A transparent sufficient lower-control hypothesis

A convenient sufficient hypothesis for (132.1) is the affine lower control

$$
\rho_e(\iota_e(x),\iota_e(y))\ge a\,d_e(x,y)-b
\tag{133.1}
$$

with fixed finite $b\ge0$ and fixed $a>0$, for all epochs and all pairs to which
the interface is applied. For an active pair, (131.3) and (133.1) imply

$$
 a\,d_e(x,y)-b\le\ell,
 \qquad	ext{hence}qquad
 d_e(x,y)\le R:=\frac{\ell+b}{a}.
\tag{133.2}
$$

After replacing $R$ by its ceiling when needed, Theorem 132.1 applies. The
affine estimate is only a transparent sufficient special case. It is not
necessary, it is not asserted to be a full quasi-isometry, and no upper
control of $\rho_e$ by $d_e$ is used. More generally, a uniform
nondecreasing lower control

$$
\rho_e(\iota_e(x),\iota_e(y))\ge\Phi(d_e(x,y)),
\qquad \Phi(t)\longrightarrow+\infty,
\tag{133.3}
$$

would give the same conclusion whenever one fixes $\ell$ and chooses a
finite $R$ with $\Phi(t)>\ell$ for $t>R$. This alternative remains
conditional on the stated uniform control and does not add a physical
interpretation to $\Phi$.

## 134. Prefixes, drifting constants, and logical boundaries

The uncapped quantifier in Theorem 132.1 is essential. Every finite stopped
or capped prefix has finitely many finite state spaces and therefore a finite
maximum occurrence range. It may satisfy prefix-dependent locality and
comparison constants without contradiction. For affine controls that vary
by layer or epoch, with $\ell_e\ge0$, $b_e\ge0$, and $a_e>0$, the relevant
bound is explicitly

$$
R_e=\frac{\ell_e+b_e}{a_e},
\qquad \ell_e\ge0,\quad b_e\ge0,\quad a_e>0.
\tag{134.1}
$$

A bounded supremum of this ratio over all accepted epochs still contradicts
Theorem 129.3. If the ratio is unbounded, this argument has no contradiction
left; it removes this proof of incompatibility and leaves compatibility open.

Upper compression alone cannot transfer occurrence range. For the two-point
abstract family $V_N=\{0,1\}$, set

$$
 d_N(0,1)=N,\qquad \rho_N(\iota_N(0),\iota_N(1))=1,
 \qquad
 Q_N=\begin{pmatrix}-1&1\\[2pt]1&-1\end{pmatrix}.
\tag{134.2}
$$

The positive support is local at physical radius $1$ for every $N$, while
its occurrence jump is $N$. Thus an upper-only compression or locality
statement cannot imply (132.1). This two-point family is only a logical
boundary example; it is not a §129-compatible FIB family and is not offered
as a counterexample to Theorem 129.3.

The conclusion is a conditional realization obstruction. The target sets
$X_e$ may have any dimension and may vary with $e$. No Euclidean dimension,
physical clock, continuum operator, finite propagation statement for
$\exp(tQ_e)$, global (all-epoch) irreducibility, native-edge support, or physical
three-dimensional conclusion follows. The next test is therefore concrete:
for the proposed realization, verify whether direct positive generator
support really has a uniform finite-radius bounded preimage (or a stated
sufficient lower control). If that bridge fails, Theorem 129.3 alone does
not decide physical locality.

## 135. Native orthogonal birth coordinates

The next statements use one actual accepted step from §§127--130. Write
$n=|V_e|$, $k=|B_e|$, and suppress the epoch subscript. Thus $P$ is the
actual parent selector, $T=[\,I_n;P\,]$, $W=[\,I_n\ 0;P\ I_k\,]$, and

$$
L_+=\begin{pmatrix}L+P^{\mathsf T}P&-P^{\mathsf T}\\-P&I_k\end{pmatrix},\qquad
W^{\mathsf T}L_+W=\operatorname{diag}(L,I_k).
$$

The coherent metric in residual coordinates is the matrix already supplied by
(127.3), namely

$$
{\mathscr G}:=W^{\mathsf T}G_+W
 =\begin{pmatrix}G&gq^{\mathsf T}\\qg^{\mathsf T}&K^{-1}+hqq^{\mathsf T}\end{pmatrix},\qquad
g=G\mathbf 1_n,\quad h=\mathbf 1_n^{\mathsf T}G\mathbf 1_n,\quad K=K^{\mathsf T}\succ0.
$$

Let $S=G^{1/2}$ and $S_+=G_+^{1/2}$ denote the symmetric positive square
roots. The normalized one-particle operators are

$$
H=S^{-1}LS^{-1},\qquad H_+=S_+^{-1}L_+S_+^{-1}.
$$

These are finite real symmetric matrices; complex Hilbert spaces below mean the
complexifications of the displayed real spaces.

**Definition 135.1 (residual birth chart).** Put

$$
B_0=\begin{pmatrix}-\mathbf 1_nq^{\mathsf T}\\ I_k\end{pmatrix},\qquad
B=WB_0,\qquad
V=S_+TS^{-1},\qquad
Z=S_+BK^{1/2},\qquad U=[\,V\ Z\,].
$$

For $k=0$, these formulas are read with the unique empty matrices and $U=V$.
The columns of $B$ are the actual-coordinate birth directions, while $B_0$
is their residual-coordinate representative.

**Proposition 135.2 (explicit orthogonal complement).** For every real $q$ and
every symmetric positive-definite $K$ allowed by (127.3),

$$
V^{\mathsf T}V=I_n,\qquad V^{\mathsf T}Z=0,\qquad Z^{\mathsf T}Z=I_k,\qquad
U^{\mathsf T}U=I_{n+k}.
$$

Consequently $U$ is unitary after complexification.

**Proof.** Let $E=[\,I_n;0\,]$, so that $T=WE$. Direct multiplication with
the displayed $\mathscr G$ gives

$$
E^{\mathsf T}\mathscr G B_0=0,\qquad B_0^{\mathsf T}\mathscr G B_0=K^{-1}.
$$

Indeed, the upper block in the first identity is
$-G\mathbf1_nq^{\mathsf T}+gq^{\mathsf T}=0$, and the Schur-complement
part of the second identity is exactly $K^{-1}$. Since
$T^{\mathsf T}G_+T=G$, $T^{\mathsf T}G_+B=0$, and
$B^{\mathsf T}G_+B=K^{-1}$. Therefore

$$
\begin{aligned}
V^{\mathsf T}V&=S^{-1}T^{\mathsf T}G_+TS^{-1}=I_n,\\
V^{\mathsf T}Z&=0,\qquad
Z^{\mathsf T}Z=K^{1/2}K^{-1}K^{1/2}=I_k.
\end{aligned}
$$

There are $n+k$ orthonormal columns in an $(n+k)$-dimensional space, so $U$
is orthogonal over the reals and unitary after complexification. $\square$

**Proposition 135.3 (native spectral normal form).** The matrices in
Definition 135.1 satisfy

$$
H_+V=VH,\qquad H_+Z=ZK,\qquad
U^{\mathsf T}H_+U=H\mathbin{\oplus}K.
$$

**Proof.** Corollary 127.3 gives the residual generator

$$
\widetilde A_+=\begin{pmatrix}A&-\mathbf1_na^{\mathsf T}\\0&K\end{pmatrix},\qquad
A=G^{-1}L,\quad a=Kq,
$$

and the source hypotheses give $A_+T=TA$. Since $A\mathbf1_n=0$ and
$K=K^{\mathsf T}$,

$$
\begin{aligned}
\widetilde A_+B_0
&=\begin{pmatrix}A&-\mathbf1_na^{\mathsf T}\\0&K\end{pmatrix}
  \begin{pmatrix}-\mathbf1_nq^{\mathsf T}\\ I_k\end{pmatrix}\\
&=\begin{pmatrix}-\mathbf1_nq^{\mathsf T}K\\ K\end{pmatrix}
=B_0K.
\end{aligned}
$$

Conjugating by $W$ yields $A_+B=BK$. Using
$L_+=G_+A_+$ and $L=GA$, the two generator identities become

$$
\begin{aligned}
H_+V&=S_+^{-1}L_+TS^{-1}=S_+TAS^{-1}=VH,\\
H_+Z&=S_+^{-1}L_+BK^{1/2}=S_+BK^{3/2}=ZK.
\end{aligned}
$$

The three block entries of $U^{\mathsf T}H_+U$ are therefore $H$, $0$, and
$K$, which proves the direct-sum identity. $\square$

Thus every bounded Borel functional calculus expression has the same
intertwining. In particular, for $s\ge0$ and $\tau\in\mathbb R$,

$$
e^{-sH_+}V=Ve^{-sH},\qquad e^{-sH_+}Z=Ze^{-sK},\qquad
e^{-i\tau H_+}V=Ve^{-i\tau H},\qquad e^{-i\tau H_+}Z=Ze^{-i\tau K}.
$$

These are finite matrix identities with the semigroup or unitary parameter
separate from the accepted epoch index.

The vector

$$
c=S\mathbf1_n/\sqrt h
$$

is the normalized old constant mode. Because $T\mathbf1_n=\mathbf1_{n+k}$ and
$T^{\mathsf T}G_+T=G$,

$$
c_+=S_+\mathbf1_{n+k}/\sqrt h=Vc,\qquad Hc=0,\qquad H_+c_+=0.
$$

Connectedness in §§127--130 gives $\ker L=\mathbb R\mathbf1_n$ and the same
one-dimensional kernel for $L_+$. Since $K\succ0$, the direct-sum form shows
that no new zero mode is present. The parameter $q$ changes the actual birth
embedding through

$$
B=WB_0=\begin{pmatrix}-\mathbf1_nq^{\mathsf T}\\
I_k-\mathbf1_kq^{\mathsf T}\end{pmatrix};
$$

it is a shear through the old constant direction. The spectral block $K$ and
the direct-sum spectrum are unchanged, but no gauge or observable equivalence
is asserted for the different coordinate embeddings.

For $k=0$, $B,Z,K$ are absent and the construction is the identity. For the
$n=1$ beta singleton, $L=0$ and the same calculation accepts every real $q$
and every SPD $K$. The first alpha-singleton step is an empty birth and hence
uses the $k=0$ identity; its later nonempty step is covered by the singleton
calculation. The same statements apply to every finite stopped or capped
accepted prefix, including a final empty-birth step.

## 136. Finite-mode Fock correspondence

Let $\mathfrak h_o=\mathbb C^n$, $\mathfrak h_b=\mathbb C^k$, and
$\mathfrak h_+=\mathbb C^{n+k}$. For $\sigma\in\{+,-\}$ write

$$
\mathcal F_\sigma(\mathfrak h)=\bigoplus_{r=0}^{\infty}
\mathfrak h_\sigma^{(r)},\qquad
\mathfrak h_+^{(r)}=\operatorname{Sym}^r\mathfrak h,\quad
\mathfrak h_-^{(r)}=\bigwedge^r\mathfrak h,
$$

with vacuum $\Omega$ in the $r=0$ sector. This is the full standard finite-mode
Fock space: the one-particle mode space is finite, but the bosonic particle
sectors are not truncated.

The finite-dimensional unitary $U:\mathfrak h_o\oplus\mathfrak h_b\to
\mathfrak h_+$ induces $\Gamma_\sigma(U)$. Let

$$
E_\sigma:\mathcal F_\sigma(\mathfrak h_o\oplus\mathfrak h_b)
\longrightarrow
\mathcal F_\sigma(\mathfrak h_o)\otimes\mathcal F_\sigma(\mathfrak h_b)
$$

be the canonical exponential law with the old modes ordered before the birth
modes, and set

$$
Q_\sigma=\Gamma_\sigma(U)E_\sigma^{-1}.
$$

Then $Q_\sigma$ is unitary and, for every old Fock vector $\psi$,

$$
\Gamma_\sigma(V)\psi=Q_\sigma(\psi\otimes\Omega_b).
$$

For the exterior case the old-first ordering fixes all fermionic signs. The
second-quantized operators below are even, so no additional sign convention
enters their tensor-product intertwining.

**Proposition 136.1 (second-quantized native lift).** On the algebraic
finite-particle core $\mathcal D_{\mathrm{fin}}$,

$$
Q_\sigma^*d\Gamma_\sigma(H_+)Q_\sigma
=d\Gamma_\sigma(H)\otimes I+I\otimes d\Gamma_\sigma(K).
$$

The equality extends to the self-adjoint closures on their natural domains.

**Proof.** On the $r$-particle sector,

$$
d\Gamma_r(X)=\sum_{j=1}^r
I\otimes\cdots\otimes X^{(j)}\otimes\cdots\otimes I.
$$

The one-particle equality $U^{\mathsf T}H_+U=H\oplus K$ transports each slot
of this sum. The exponential law separates the old and birth slots, giving the
two commuting summands on $\mathcal D_{\mathrm{fin}}$. The core is invariant
under all finite-mode second quantizations, and closure gives the stated
self-adjoint identity. $\square$

For bosons, if $\psi=(\psi_r)_{r\ge0}$, the self-adjoint domain is

$$
\mathcal D(d\Gamma_+(H))
=\left\{\psi:\sum_{r\ge0}\|d\Gamma_r(H)\psi_r\|^2<\infty\right\},
$$

and analogously for $H_+$ and $K$. Finite-particle vectors form a core. Under
$Q_+$ the domain of the tensor sum is the intersection domain of its two
commuting self-adjoint summands, with the same weighted sector condition. For
fermions, $\dim\mathcal F_-(\mathbb C^m)=2^m$; hence all finite-mode
$d\Gamma_-(X)$ are bounded and the whole exterior Fock space is their domain.
These are finite-prefix statements and do not take an infinite-native-epoch
limit.

The generic Fock maps and vacuum facts used here are the existing
D5/S3/Quantum/PassiveFockModel.lean declarations; the finite occupation
identities are the existing
D5/S3/Quantum/FockSpace/FiniteOccupationPartitionFunctions.lean route.
The direct-sum exponential law and $d\Gamma$ slot sum are treated in Jan
Dereziński, *Mathematical Introduction to Quantum Field Theory*, §§5.2--5.4,
5.7 and Theorem 5.3 (§5.9),
[PDF](https://users.fuw.edu.pl/~derezins/qft-lectures.pdf). The domain and core
terminology is consistent with Dereziński, *Mathematical Topics in Many Body
Quantum Physics*, §§1.1--1.5,
[PDF](https://users.fuw.edu.pl/~derezins/manybody.pdf). Those references supply
the generic Fock constructions; the native matrices and the $U$ above are the
source-dependent content of this continuation.

## 137. Finite-prefix thermal boundary

Fix a scalar parameter $\beta>0$. The following is a finite matrix trace
statement; $\beta$ is not identified with a physical temperature, and the
eigenvalues of $H$ are not declared physical energies.

Let $\mathfrak h_o^\circ=c^\perp$ and
$\mathfrak h_+^\circ=c_+^\perp$. Since $c_+=Vc$, $V^*V=I$ and
$Z^*V=0$, Proposition 135.2 gives the orthogonal decomposition

$$
\mathfrak h_+^\circ
=V(\mathfrak h_o^\circ)\mathbin{\oplus^\perp}\operatorname{Ran}Z.
$$

The summands have dimensions $n-1$ and $k$, respectively.
Indeed, the unique representation $x=Vv+Zb$ supplied by $U$ satisfies
$\langle c_+,x\rangle=\langle c,v\rangle$, so $x\perp c_+$ exactly when
$v\perp c$. In particular the restricted map

$$
U^\circ:\mathfrak h_o^\circ\oplus\mathfrak h_b
\longrightarrow\mathfrak h_+^\circ,\qquad
U^\circ(v,b)=Vv+Zb
$$

is unitary. Symmetry makes the constant-orthogonal spaces invariant, and
Proposition 135.3 restricts to

$$
(U^\circ)^*\bigl(H_+|_{\mathfrak h_+^\circ}\bigr)U^\circ
=H|_{\mathfrak h_o^\circ}\oplus K.
$$

The positive semidefinite native forms, their connected constant kernels and
$K\succ0$ make both restricted one-particle operators positive definite on
their possibly zero-dimensional
spaces. For $n=1$, $\mathfrak h_o^\circ=\{0\}$ and
$\mathfrak h_+^\circ=\operatorname{Ran}Z$, so the restricted operator is
unitarily equivalent to $K$. In particular the $n=k=1$ matrix case has one
positive birth mode; this algebraic case does not add an allowed native birth
cardinality to Definition 127.1. For $k=0$, $\operatorname{Ran}Z=\{0\}$ and
$U^\circ=V|_{\mathfrak h_o^\circ}$. The Fock space of a zero-dimensional
mode space consists only of its vacuum and has trace $1$; empty birth
determinants are $1$. The unrestricted
bosonic full-Fock trace for $H$ diverges, because arbitrary occupation of the
constant mode contributes the same factor $1$ in every particle sector. Thus
there is no legitimate infinity-over-infinity ratio between old and new traces.

After the compatible constant-kernel removal above, the finite birth factors
are

$$
Z_{+,\mathrm{birth}}(\beta;K)
=\det(I_k-e^{-\beta K})^{-1},\qquad
Z_{-,\mathrm{birth}}(\beta;K)
=\det(I_k+e^{-\beta K}).
$$

The restricted bosonic trace factorizes as

$$
\operatorname{Tr}\!\left(e^{-\beta d\Gamma_+(H_+|_{\mathfrak h_+^\circ})}\right)
=\operatorname{Tr}\!\left(e^{-\beta d\Gamma_+(H|_{\mathfrak h_o^\circ})}\right)
\det(I_k-e^{-\beta K})^{-1},
$$

and the corresponding fermionic identity uses $\det(I_k+e^{-\beta K})$.
The formula is spectral, so no diagonal choice for $K$ is required. In the
unrestricted fermionic finite-mode space the old zero mode causes no
divergence; retaining or removing it is a separately stated boundary choice.

If instead the total particle number is fixed to $r$, the correct statement is
a finite convolution. With $Z_{\sigma,j}(X)$ denoting the $j$-particle trace,

$$
Z_{\sigma,r}(H\oplus K)=\sum_{a+b=r}Z_{\sigma,a}(H)Z_{\sigma,b}(K),
$$

with the terms outside the available fermionic dimensions interpreted as zero.
This fixed-number identity does not become an unrestricted product ratio. The
spectral normal form is valid for all real $q$ and SPD $K$ permitted by §127;
the Markov positivity restrictions in Proposition 128.2 are an independent
source-specific condition and are not inferred from this thermal calculation.

## 138. Boundary ledger for the native lift

The construction is defined for every finite accepted prefix in the source
quantifier of Definition 127.1. Empty births have $k=0$ and preserve the old
one-particle and Fock factors by the identity. The alpha singleton has its
initial empty step before its first nonempty birth; the beta singleton has the
nonempty $n=1$ step directly, with arbitrary $q$ and SPD $K$. A stopped or
capped history requires no later epoch. The bosonic domain above retains all
particle sectors, while the phrase “finite mode” refers only to the dimension
of the one-particle space.

No assertion here concerns an infinite-epoch or quantum-field limit, locality,
physical propagation, a physical Hamiltonian, charge, priority, resource
equivalence, or an observable/gauge identification of different $q$. The
mathematical claims are the native finite-dimensional unitary normal form, its
standard full-Fock lift, and the stated finite trace boundaries.

## 138.99 追加锚（本行以下为增补区）
## 139. A native two-child application with two interior Markov metrics

The following application fixes one finite accepted history and compares two
metrics on its unchanged occurrence form. It uses the native parameter class
of Proposition 127.2, rather than selecting an abstract two-mode birth.
Start with the singleton source $\beta$ at epoch $0$, with $G_0=[1]$ and
$L_0=[0]$. Its accepted substitution is
$\beta\mapsto\langle\beta,\alpha\rangle$; the distinct born occurrences
are $L$ and $R$. Stop at epoch $1$. In actual-coordinate order
$(r,\ell,R)=(\varepsilon,L,R)$, the source data are

$$
n=1,\quad k=2,\quad
P=\begin{pmatrix}1\\1\end{pmatrix},\quad
T=\mathbf1_3,\quad K=I_2,\quad
W=\begin{pmatrix}1&0&0\\1&1&0\\1&0&1\end{pmatrix},\quad
L_\star=\begin{pmatrix}2&-1&-1\\-1&1&0\\-1&0&1\end{pmatrix}.
\tag{139.1}
$$

Thus $P^{\mathsf T}P=2$, as required by the actual beta birth in
Definition 130.1. A singleton has no branch-port entry record, and none is
introduced here. Proposition 128.3 permits this stopped history directly.
Write $q=(u,v)^{\mathsf T}$ and
$\pi_q=(1-u-v,u,v)^{\mathsf T}$. With the inherited scalar norm fixed,
(127.3) becomes

$$
W^{\mathsf T}G_qW=
\begin{pmatrix}1&q^{\mathsf T}\\q&I_2+qq^{\mathsf T}\end{pmatrix},
\qquad
x^{\mathsf T}G_qx=(\pi_q^{\mathsf T}x)^2
 +(x_\ell-x_r)^2+(x_R-x_r)^2,
\qquad G_q=L_\star+\pi_q\pi_q^{\mathsf T}.
\tag{139.2}
$$

Indeed $W^{-1}x=(x_r,x_\ell-x_r,x_R-x_r)$, so the residual quadratic
form is $(a+q^{\mathsf T}y)^2+\|y\|^2$. Its vanishing forces $x=cT$
and then $c=\pi_q^{\mathsf T}x=0$. Hence $G_q\succ0$; its determinant
is $1$ by the residual Schur complement. The useful native identities are

$$
L_\star T=0,\quad \pi_q^{\mathsf T}T=1,\quad G_qT=\pi_q,
\quad T^{\mathsf T}G_qT=1,\quad
Q_q=-G_q^{-1}L_\star=T\pi_q^{\mathsf T}-I_3.
\tag{139.3}
$$

The last equality follows by multiplying $I_3-T\pi_q^{\mathsf T}$ by
$G_q$. It gives the exact old norm, form and generator comparison:
$T^{\mathsf T}L_\star T=0$ and $G_q^{-1}L_\star T=0$.
The generator acts on functions as a row-generator matrix, with
$Q_qT=0$ and stationary row probability $\pi_q^{\mathsf T}Q_q=0$.
For $u,v\ge0$ and $u+v\le1$ its off-diagonal rates are $(Q_q)_{ij}=
(\pi_q)_j\ge0$. The two choices used below lie strictly inside this simplex:

$$
q_a=(1/6,1/6)^{\mathsf T},\quad \pi_a=(2/3,1/6,1/6)^{\mathsf T},
\qquad q_b=(1/3,1/3)^{\mathsf T},\quad \pi_b=T/3,
\tag{139.4}
$$

$$
G_a=\frac1{36}\begin{pmatrix}88&-32&-32\\-32&37&1\\-32&1&37\end{pmatrix},
\qquad G_b=\frac1{9}\begin{pmatrix}19&-8&-8\\-8&10&1\\-8&1&10\end{pmatrix},
\tag{139.5}
$$

$$
Q_a=\frac1{6}\begin{pmatrix}-2&1&1\\4&-5&1\\4&1&-5\end{pmatrix},
\qquad Q_b=\frac1{3}\begin{pmatrix}-2&1&1\\1&-2&1\\1&1&-2\end{pmatrix}.
\tag{139.6}
$$

Every off-diagonal rate is positive in both matrices; both finite Markov
models are conservative and irreducible. They have sibling transitions,
so neither is asserted to have original-star-edge support. This first-step
statement asserts no irreducibility at subsequent accepted epochs.

## 140. Principal-root normalization and the declared common cut

For each metric use its positive principal square root $S_q=G_q^{1/2}$,
normalize by $z=S_qx$, and then complexify the normalized real space to
$\mathfrak h=\mathbb C^3$ with its standard Hermitian product. Define

$$
V_q=S_qT,\qquad \|V_q\|^2=1,\qquad
H_q=S_q^{-1}L_\star S_q^{-1}=I_3-V_qV_q^*,
\qquad \operatorname{spec}H_q=\{0,1,1\}.
\tag{140.1}
$$

Here $*$ is complex adjoint; the displayed vectors are real. To obtain the
rank-one formula, use $\pi_q^{\mathsf T}S_q^{-1}=T^{\mathsf T}S_q$ in
$H_q=S_q(G_q^{-1}L_\star)S_q^{-1}$. This fixes the normalization:
an arbitrary metric factor followed by an unspecified unitary would not
fix the coordinate cut used below.

For $q_a$, the antisymmetric direction $(0,1,-1)/\sqrt2$ has $G_a$
eigenvalue $1$. In the orthonormal symmetric basis
$(e_r,(e_\ell+e_R)/\sqrt2)$ the other block is

$$
M_a=\begin{pmatrix}22/9&-8\sqrt2/9\\-8\sqrt2/9&19/18\end{pmatrix},
\qquad \det M_a=1,\quad \operatorname{tr}M_a=7/2,
\qquad M_a^{1/2}=\frac{M_a+I_2}{\sqrt{11/2}}.
\tag{140.2}
$$

Cayley--Hamilton gives $(M_a+I_2)^2=(\operatorname{tr}M_a+2)M_a$;
$M_a+I_2$ is positive, so this is the principal root. Since $T$ is
symmetric under exchange of the children, it follows that

$$
V_a=\frac{\pi_a+T}{\sqrt{11/2}}
 =\frac{(10,7,7)^{\mathsf T}}{\sqrt{198}},\qquad
G_bT=T/3,\qquad V_b=T/\sqrt3.
\tag{140.3}
$$

Use the same normalized coordinate labels in both models and declare

$$
A=\mathbb C e_\ell,\qquad
B=\operatorname{span}_{\mathbb C}\{e_r,e_R\},\qquad
\mathfrak h=A\oplus B,\qquad
p_q=|(V_q)_\ell|^2,\quad p_a=49/198,\quad p_b=1/3.
\tag{140.4}
$$

This is a common cut of the declared normalized axes. The principal-root
map can mix actual coordinates, so it does not identify this cut with
orthogonal raw weighted occurrence spans or physical spatial subsystems.
Its use is part of the finite quantum model being specified.

The boundary comparison $q_0=(0,0)$ retains
$\pi_0=(1,0,0)^{\mathsf T}$ and
$V_0=(2,1,1)^{\mathsf T}/\sqrt6$, hence $p_0=1/6$.
Its root is absorbing and its Markov generator is reducible. Its ordinary
separability comparison with $q_b$ at inverse temperature $\log7$ remains
valid; it is not relabeled as an interior or irreducible example.
The pair (139.4) supplies the comparison with both rate graphs irreducible.

## 141. Full finite fermionic Gibbs states and their common scalars

Take the entire fermionic Fock space and retain the zero-energy mode:

$$
\mathcal F_-(\mathfrak h)=\bigoplus_{j=0}^3\Lambda^j\mathfrak h,
\quad \dim\mathcal F_-(\mathfrak h)=1+3+3+1=8,\quad
\widehat H_q=d\Gamma_-(H_q),\quad
\rho_{q,\beta}=\frac{e^{-\beta\widehat H_q}}{Z_\beta}.
\tag{141.1}
$$

There is no chemical-potential term or sector conditioning. Here $\beta$
denotes inverse temperature, distinct from the source symbol $\beta$.
Set $t=e^{-\beta}$ for finite $\beta\ge0$. In eigenmode occupations
$(m_0,m_1,m_2)\in\{0,1\}^3$, the energy is $m_1+m_2$, giving

$$
e^{-\beta d\Gamma(H_q)}=\Gamma(e^{-\beta H_q}),\qquad
Z_\beta=\sum_{m_0,m_1,m_2=0}^1t^{m_1+m_2}=2(1+t)^2.
\tag{141.2}
$$

This is the finite occupation application of the fermionic Fock exponential
and direct-sum laws in Dereziński, §§5.7 and 5.9, Theorem 5.3 [F].
The contributions to the trace by total particle number are

$$
Z^{(0)}=1,\qquad Z^{(1)}=1+2t,\qquad
Z^{(2)}=2t+t^2,\qquad Z^{(3)}=t^2.
\tag{141.3}
$$

They sum to (141.2). The zero eigenmode has occupation $1/2$; each unit
mode has occupation $f_\beta=t/(1+t)$. For covariance convention
$(C_q)_{ij}=\operatorname{Tr}(\rho_{q,\beta}a_j^\dagger a_i)$,

$$
C_{q,\beta}=(I_3+e^{\beta H_q})^{-1}
 =f_\beta I_3+(1/2-f_\beta)V_qV_q^*.
\tag{141.4}
$$

Consequently the following four scalars agree between the two models at
every such inverse temperature:

$$
Z_\beta=2(1+t)^2,\qquad
E_\beta=\operatorname{Tr}(\rho\widehat H_q)=\frac{2t}{1+t},\qquad
N_\beta=\operatorname{Tr}(\rho d\Gamma(I_3))=\frac12+\frac{2t}{1+t},
\qquad P_{111,\beta}=\frac{t^2}{2(1+t)^2}.
\tag{141.5}
$$

Here $P_{111,\beta}=\operatorname{Tr}(\rho n_rn_\ell n_R)$ is the
probability of the unique three-particle line. That line has energy
$\operatorname{tr}H_q=2$ in any orthonormal coordinate basis. It is not
an assertion that each coordinate occupation has the same distribution.
At the concrete inverse temperature $\beta=\log7$ these formulas give

$$
Z=128/49,\qquad E=1/4,\qquad N=3/4,\qquad P_{111}=1/128,
\tag{141.6}
$$

$$
C_a=\frac1{528}\begin{pmatrix}166&70&70\\70&115&49\\70&49&115\end{pmatrix},
\qquad
C_b=\frac1{8}\begin{pmatrix}2&1&1\\1&2&1\\1&1&2\end{pmatrix}.
\tag{141.7}
$$

The order in (141.7) is $(r,\ell,R)$ on the normalized axes. The unequal
covariances are compatible with the equal spectral scalars (141.6).
Restricting to one particle or another fixed-number sector would change
the state and its normalization; none of those conditioned states replaces
(141.1). For the full bosonic Fock space with this zero mode retained,
$\sum_{m_0=0}^\infty1$ already diverges. Thus no full bosonic Gibbs state
is obtained here. Removing the kernel or adding a chemical potential would
specify a different model.

## 142. CAR ordering and the B-local spectator factorization

Fix the A-first creation order $(\ell,r,R)$ once for both models:

$$
|n_A,n_r,n_R\rangle
 =(a_\ell^\dagger)^{n_A}(a_r^\dagger)^{n_r}
  (a_R^\dagger)^{n_R}|\mathrm{vac}\rangle,
\qquad \mathcal F_-(\mathfrak h)\cong\mathbb C^2_A\otimes\mathbb C^4_B.
\tag{142.1}
$$

This declares an ordinary occupation tensor identification. Odd CAR fields
remain graded. Put $c=|0\rangle\langle1|$ and $Z=\operatorname{diag}(1,-1)$.
The actual annihilators in this identification are

$$
a_\ell=c\otimes I_B,\qquad
 a_r=Z_A\otimes b_r,\quad a_R=Z_A\otimes b_R,
\qquad b_r=c\otimes I_2,\quad b_R=Z\otimes c.
\tag{142.2}
$$

In particular $a_i^\dagger a_j=I_A\otimes b_i^\dagger b_j$ for
$i,j\in\{r,R\}$. A number-preserving B rotation is generated by these
even bilinears and lifts to the ordinary local $I_A\otimes\Gamma(U_B)$.
The A string cancels; treating a B odd annihilator itself as $I_A\otimes b_i$
would not give this argument.

In B coordinate order $(r,R)$ choose the rotations

$$
U_{B,a}=\frac1{\sqrt{149}}\begin{pmatrix}10&-7\\7&10\end{pmatrix},
\qquad U_{B,b}=\frac1{\sqrt2}\begin{pmatrix}1&-1\\1&1\end{pmatrix}.
\tag{142.3}
$$

Their first columns are $V_B/\|V_B\|$, and their second columns are
orthogonal spectator directions. Write the new B modes as $(b,d)$ and
$\mathcal U_q=I_A\otimes\Gamma(U_{B,q})$. With
$v_p=(\sqrt p,\sqrt{1-p})^{\mathsf T}$, the one-particle transformation gives

$$
(1\oplus U_{B,q})^*V_q=(\sqrt p,\sqrt{1-p},0)^{\mathsf T},\qquad
H_{\mathrm{eff}}(p)=I_2-v_pv_p^*
 =\begin{pmatrix}1-p&-\sqrt{p(1-p)}\\-\sqrt{p(1-p)}&p\end{pmatrix},
\qquad H_q\longmapsto H_{\mathrm{eff}}(p)\oplus[1].
\tag{142.4}
$$

To pass from this block display to an ordinary Gibbs tensor product, keep
the creation order $(A,b,d)$. Every A--b bilinear acts on the first two
occupation factors, with identity on $d$. The spectator number operator is
$I_{Ab}\otimes n_d$. There is no coupling to $d$, and therefore

$$
\mathcal U_q^*\widehat H_q\mathcal U_q
 =d\Gamma(H_{\mathrm{eff}}(p))\otimes I_d+I_{Ab}\otimes n_d,
\qquad
\mathcal U_q^*\rho_{q,\beta}\mathcal U_q
 =\sigma_\beta(p)\otimes\tau_\beta,
\quad \tau_\beta=\frac{\operatorname{diag}(1,t)}{1+t}.
\tag{142.5}
$$

Both Hamiltonian summands commute. Their partition functions are
$2(1+t)$ and $1+t$, respectively. The spectator lies entirely in B.
In the effective occupation basis $(|00\rangle,|01\rangle,|10\rangle,|11\rangle)$,

$$
\sigma_\beta(p)=\frac1{2(1+t)}
\begin{pmatrix}
1&0&0&0\\
0&1-(1-t)p&(1-t)\sqrt{p(1-p)}&0\\
0&(1-t)\sqrt{p(1-p)}&t+(1-t)p&0\\
0&0&0&t
\end{pmatrix}.
\tag{142.6}
$$

The vacuum and double-occupation Boltzmann weights before normalization
are $1$ and $t$. On the one-particle sector in order $(|10\rangle,|01\rangle)$,
$e^{-\beta H_{\mathrm{eff}}}=tI_2+(1-t)v_pv_p^*$.
This gives every entry and the positive coherence sign in (142.6) with the
creation convention (142.1). No unrestricted physical local qubit control
is inferred from the occupation tensor notation.

## 143. Exact ordinary separability contrast at inverse temperature log 7

At $t=1/7$, (142.6) reads

$$
\sigma(p)=\frac1{16}\begin{pmatrix}
7&0&0&0\\0&7-6p&6\sqrt{p(1-p)}&0\\
0&6\sqrt{p(1-p)}&1+6p&0\\0&0&0&1
\end{pmatrix},\qquad \tau=\operatorname{diag}(7/8,1/8).
\tag{143.1}
$$

Partial transpose on the ordinary A factor moves the coherence to the
$|00\rangle,|11\rangle$ corner. The other two eigenvalues are the positive
numbers $(7-6p)/16$ and $(1+6p)/16$; the corner is

$$
\frac1{16}\begin{pmatrix}7&6\sqrt{p(1-p)}\\6\sqrt{p(1-p)}&1\end{pmatrix},
\qquad \det=\frac{7-36p(1-p)}{256}.
\tag{143.2}
$$

The ordinary two-qubit PPT criterion, Horodecki--Horodecki--Horodecki,
Theorem 3, PDF p. 8 [P], applies to $\sigma(p)$. Thus it is separable
exactly when $36p(1-p)\le7$. For the interior model $a$,

$$
p_a(1-p_a)=\frac{7301}{39204},\quad
36p_a(1-p_a)=\frac{7301}{1089}<7,\qquad
\sigma_a=\frac1{528}\begin{pmatrix}
231&0&0&0\\0&182&\sqrt{7301}&0\\
0&\sqrt{7301}&82&0\\0&0&0&33
\end{pmatrix}.
\tag{143.3}
$$

The PT corner determinant is $322/528^2>0$. Its full PT spectrum is

$$
\left\{\frac{182}{528},\frac{82}{528},
\frac{132+\sqrt{17102}}{528},\frac{132-\sqrt{17102}}{528}\right\},
\qquad 132^2-17102=322>0.
\tag{143.4}
$$

Hence $\sigma_a$ is separable. Tensor its product-state decomposition with
the B-local $\tau$, then undo $\mathcal U_a$: the full $2\times4$ state
$\rho_{a,\log7}$ is ordinary-tensor separable at the declared cut.
For model $b$, $36p_b(1-p_b)=8>7$, and

$$
\sigma_b=\frac1{16}\begin{pmatrix}
7&0&0&0\\0&5&2\sqrt2&0\\0&2\sqrt2&3&0\\0&0&0&1
\end{pmatrix},\qquad
\lambda_{\min}(\sigma_b^{T_A})=\frac{4-\sqrt{17}}{16}<0.
\tag{143.5}
$$

The full partial transpose has negative eigenvalues
$7(4-\sqrt{17})/128$ and $(4-\sqrt{17})/128$ after multiplication by
the spectator weights. Undoing a B-local unitary preserves NPT. Therefore
$\rho_{b,\log7}$ is ordinary-tensor entangled, despite (141.6).
This uses two-qubit PPT sufficiency only after the proved B-local
factorization. It invokes no PPT sufficiency for arbitrary $2\times4$ states.
For the retained boundary model $p_0=1/6$, the same scalar test gives
$36p_0(1-p_0)=5<7$, consistently with its separability and reducibility.

## 144. Finite-temperature boundaries for this same native family

For finite $\beta\ge0$, the PT of (142.6) has positive singleton entries
and the corner block

$$
\frac1{2(1+t)}\begin{pmatrix}
1&(1-t)\sqrt{p(1-p)}\\(1-t)\sqrt{p(1-p)}&t
\end{pmatrix}.
\tag{144.1}
$$

Its determinant has the sign of $t-(1-t)^2p(1-p)$. Applying the same
two-qubit criterion and the B-local spectator factorization gives, for the
states specified in (142.5), the exact alternatives

$$
\rho_{q,\beta}\text{ separable}
\ \Longleftrightarrow\ (1-t)^2p(1-p)\le t
\ \Longleftrightarrow\ 4\sinh^2(\beta/2)p(1-p)\le1;
\quad \rho_{q,\beta}\text{ NPT otherwise}.
\tag{144.2}
$$

Here $(1-t)^2/t=e^\beta+e^{-\beta}-2=4\sinh^2(\beta/2)$.
For $p=0$ or $p=1$ the effective state is a product for every finite
$\beta$: it is respectively
$\operatorname{diag}(1,t)/(1+t)\otimes I_2/2$ or
$I_2/2\otimes\operatorname{diag}(1,t)/(1+t)$.
These endpoint statements concern the effective rank-one family; they do
not assert that either endpoint occurs in the interior pair (139.4).
For $0<p<1$ define

$$
\beta_c(p)=2\operatorname{arsinh}\frac1{2\sqrt{p(1-p)}},\qquad
\beta_{c,a}=2\operatorname{arsinh}\frac{99}{\sqrt{7301}},\qquad
\beta_{c,b}=2\operatorname{arsinh}\frac3{2\sqrt2}.
\tag{144.3}
$$

Since $p_a(1-p_a)<p_b(1-p_b)$, one has $\beta_{c,b}<\beta_{c,a}$.
Monotonicity of $\sinh(\beta/2)$ gives the complete finite-temperature
classification of this pair:

| Inverse-temperature interval | Model $a$ | Model $b$ |
| --- | --- | --- |
| $0\le\beta\le\beta_{c,b}$ | separable | separable |
| $\beta_{c,b}<\beta\le\beta_{c,a}$ | separable | NPT |
| $\beta>\beta_{c,a}$, finite | NPT | NPT |

Equality at either threshold is PPT and separable for that effective
state. The exact tests (143.3) and (143.5) place $\log7$ strictly between
the thresholds. At $\beta=0$, $\rho=I_8/8$ in both models.
At every inverse temperature in the table, the thermodynamic expressions
(141.5) remain common. The table is an application to this finite native
family and its declared cut, rather than a classification of general
fermionic Gibbs states or of all source histories.

## 145. The single-copy local number and parity SSR limit

Ordinary tensor entanglement and local SSR-accessible entanglement are
different questions for (142.1). On the single A mode, both number- and
parity-preserving observables form $\operatorname{span}\{I,n_A\}$.
Put $P_a=|a\rangle\langle a|$ for $a=0,1$.
The number twirl and parity twirl on A consequently coincide:

$$
\mathcal D_A(\rho)=\sum_{a=0}^1(P_a\otimes I_B)\rho(P_a\otimes I_B)
 =\sum_{a=0}^1|a\rangle\langle a|\otimes R_a,
\quad R_a=\langle a|\rho|a\rangle\ge0,\quad
\sum_a\operatorname{Tr}R_a=1.
\tag{145.1}
$$

This is explicitly separable: whenever $w_a=\operatorname{Tr}R_a>0$,
its term is $w_a|a\rangle\langle a|\otimes(R_a/w_a)$.
In the aligned B basis of (142.5), the unnormalized conditional blocks are

$$
R_0=\frac{\operatorname{diag}(1,1-(1-t)p)}{2(1+t)}\otimes\tau_\beta,
\qquad
R_1=\frac{\operatorname{diag}(t+(1-t)p,t)}{2(1+t)}\otimes\tau_\beta.
\tag{145.2}
$$

Both commute with B number. Undoing the number-preserving B rotation
preserves this fact, so an additional local B number or parity twirl leaves
(145.1) unchanged. In particular at $t=1/7$ these blocks are
$\operatorname{diag}(7,7-6p)\otimes\tau/16$ and
$\operatorname{diag}(1+6p,1)\otimes\tau/16$.

For allowed local product observables $X_A,Y_B$ one has
$\operatorname{Tr}[\rho(X_A\otimes Y_B)]
=\operatorname{Tr}[\mathcal D_A(\rho)(X_A\otimes Y_B)]$.
The effective coherence $|10\rangle\langle01|$ changes A occupation and
is removed. Thus single-copy protocols restricted to these local SSR
resources have the separable representative (145.1). In this resource
model the ordinary NPT of $\rho_b$ supplies no locally accessible
single-copy entanglement. Local forbidden coherences are not assumed
available as operations or measurements.

SSR restriction does not make the two models statistically identical.
The allowed occupation measurement already gives, at $\beta=\log7$,

$$
\langle n_A\rangle_a=\frac18+\frac38\frac{49}{198}
 =\frac{115}{528},\qquad
\langle n_A\rangle_b=\frac18+\frac38\frac13=\frac14.
\tag{145.3}
$$

Accordingly equal $Z,E,N,P_{111}$ do not imply equality of all statistics,
even within the allowed local observable algebra. Shared coherence
references, multiple copies, and unrestricted spin-qubit realizations
specify additional resource models. Their availability or benefit is not
derived here. Wiseman--Vaccaro [S], Eqs. (12)--(14) and Table I, supply
resource context; the mixed-state statement here follows from the explicit
twirl, without importing a pure-state formula as a mixed-state criterion.

## 146. Source correspondence, references and applicability

The native input is exactly the singleton beta step of Definition 127.1
and Proposition 128.3, with the two actual children and unchanged edge form
in (139.1). Formula (139.2) substitutes $G_0=[1]$, $K=I_2$ and the stated
$q$ into (127.3); (139.3) specializes Corollary 127.3. The inherited norm,
accepted history, edge weights, comparison clock and $K$ are common.
Only the residual cross vector and the resulting state metric vary.
The complexification, principal-root coordinate normalization, occupation
tensor convention and normalized A|B cut are explicitly added finite
quantum-model data. They are not inferred physical encodings.

The resulting contrast concerns full finite fermionic Gibbs states and
ordinary tensor separability at that cut, with the SSR limit (145.1).
Neither the accepted epoch nor inverse temperature is thereby identified
with a physical clock. The locality interface of §§131--134 still requires
its own physical realization and uniform comparison hypotheses; this finite
stopped example supplies no such bridge. No continuum or infinite-Fock
limit, Bell violation, SSR operational advantage, literature priority,
Lean kernel certificate or completion of a broader quantum programme is
asserted. The external Fock and two-qubit criteria below are reused
established results; their finite source-parameter application is what the
displayed calculations specify.

- **[N] Native source.** This volume, Definition 127.1, Proposition 127.2,
  Corollary 127.3, Proposition 128.3 and Definition 130.1:
  [immutable native metric source](https://github.com/the-omega-institute/trureturing/blob/28e2ace3ee3cb91ebd90e1c7da0bec381b109e52/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VI.md).
  The realization limits are §§131--134 in the
  [immutable locality source](https://github.com/the-omega-institute/trureturing/blob/30b32d5e17e23590839090a0b244c019c4796817/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VI.md).
- **[F] Fermionic Fock ingredients.** Jan Dereziński,
  [qft-lectures](https://www.fuw.edu.pl/~derezins/qft-lectures.pdf),
  §§5.7 and 5.9, Theorem 5.3. Used for fermionic Fock, second quantization
  and the exponential/direct-sum laws, with the finite occupations and CAR
  locality displayed in §§141--142.
- **[P] Ordinary two-qubit separability.** M. Horodecki, P. Horodecki and
  R. Horodecki, *Separability of Mixed States: Necessary and Sufficient
  Conditions*, [quant-ph/9605038v2](https://arxiv.org/pdf/quant-ph/9605038v2),
  Theorem 3, PDF p. 8; DOI
  [10.1016/S0375-9601(96)00706-2](https://doi.org/10.1016/S0375-9601(96)00706-2).
  PPT sufficiency is used only on the effective $2\times2$ state.
- **[S] SSR resource context.** H. M. Wiseman and J. A. Vaccaro,
  [quant-ph/0210002v2](https://arxiv.org/pdf/quant-ph/0210002v2),
  Eqs. (12)--(14) and Table I. The explicit single-copy mixed-state twirl
  (145.1)--(145.2) carries the SSR conclusion used here.

## 146.99 追加锚（本行以下为增补区）
## 147. Quantitative robustness of the normalized bound state

The strict gap in Theorem 55.4 also has a perturbative meaning. This
section keeps the common rooted carrier, counting measure, inherited seams
and normalization of §§55.1--55.5 fixed; §138 supplies the later native-lift
ledger. A perturbation below is only a
bounded real multiplication operator on that carrier; it is not a new
physical field, a change of source history, or a claim about a spatial
dimension.

For a bounded real sequence $w=(w(p))_{p\in\mathcal P}$, write

$$
W_w f(p)=w(p)f(p),
\qquad
\delta_w=\|W_w\|=\sup_{p\in\mathcal P}|w(p)|,
\qquad
\mathsf H_w=\mathsf H+W_w.
\tag{147.1}
$$

Let

$$
m_w=\inf_{\|f\|=1}\langle f,\mathsf H_wf\rangle.
\tag{147.2}
$$

The finite restriction on an actual domain $D_j(t)$ is obtained by
compressing both $\mathsf H$ and the same multiplication operator $W_w$;
write its quadratic form as

$$
\mathcal E_{D_j,w}(f)=\mathcal E_{D_j}(f)+\langle I_{D_j}f,W_wI_{D_j}f\rangle
$$

and denote its normalized minimum by $m_{j,w}(t)$. No stage-dependent
renormalization of $w$ is made.

**Theorem 147.1 (uniform bounded-potential robustness).** Let

$$
\Delta=\epsilon_*-m>0,
\qquad
0\le\delta_w<\frac{\Delta}{2},
\tag{147.3}
$$

where $m$ and $\epsilon_*=a(3-2\sqrt2)$ are the common infimum and escape
edge of §§55.3--55.4. Then

1. $m_w<\epsilon_*-\delta_w$ and the normalized infimum $m_w$ is attained;
2. every normalized $\mathsf H_w$-minimizing sequence has a strongly
   convergent subsequence in $\ell^2(\mathcal P)$, and every cluster point is
   a normalized ground state;
3. for every fixed original source $t$, $m_{j,w}(t)\downarrow m_w$ as the
   actual whole-$\rho$ domains exhaust the common carrier; if $f_j$ is any
   normalized finite state satisfying
   $\mathcal E_{D_j,w}(f_j)-m_{j,w}(t)\to0$, their zero extensions are
   strongly precompact and their cluster points are common normalized ground
   states.

For any sequence of original sources and accepted indices $(t_n,j_n)$ whose
contained ball radii tend to infinity, the corresponding minimum values
converge to $m_w$ and normalized near-minimizers have the same strong
precompactness conclusion, with the same fixed $w$ and common embedding; no
monotonicity is asserted for this varying sequence.

**Proof.** The bounded perturbation gives the two elementary Rayleigh
inequalities

$$
m-\delta_w\le m_w\le m+\delta_w.
\tag{147.4}
$$

The second inequality follows by evaluating $\mathsf H_w$ on a normalized
near-minimizer of $\mathsf H$; the first is the analogous lower estimate.
For a normalized sequence $f_n\rightharpoonup f$, put
$r_n=f_n-f$ and $\alpha=\|f\|^2$. The compactness of $M_\phi$ and the
boundedness of $W_w$ make all mixed terms tend to zero. The kinetic gap in
(55.10), together with $W_w\ge-\delta_wI$, therefore gives

$$
\liminf_n\langle f_n,\mathsf H_wf_n\rangle
\ge
\langle f,\mathsf H_wf\rangle
+(\epsilon_*-\delta_w)(1-\alpha).
\tag{147.5}
$$

Since $\langle f,\mathsf H_wf\rangle\ge m_w\alpha$, a minimizing sequence
and (147.4) imply

$$
m_w
\ge m_w\alpha+(\epsilon_*-\delta_w)(1-\alpha),
\qquad
\epsilon_*-\delta_w-m_w
\ge\Delta-2\delta_w>0.
\tag{147.6}
$$

Consequently $\alpha=1$. Weak convergence is then strong convergence, and
the limit attains $m_w$. The same calculation applies to every normalized
near-minimizer, proving the second assertion.

For the finite restrictions, zero extension identifies each finite Rayleigh
quotient with the common quadratic form on its support. Nested exhaustion
gives $m_{j,w}(t)\ge m_w$ and monotonicity. A finite-support approximation to
any common unit trial gives the reverse limiting inequality, so
$m_{j,w}(t)\downarrow m_w$. Finite near-minimizers are consequently common
near-minimizers, and (147.5)--(147.6) gives strong precompactness. The varying
source statement uses exactly the same contained-ball argument as (55.13),
with no change to the common embedding. $\square$

The radius in (147.3) is a certified worst-case margin, not an optimal
radius for each particular $w$. It is nevertheless a new distinction from
finite negativity: the quantity that protects normalization is the distance
from the infinite minimum to the escape edge, and a perturbation consumes at
most two copies of its operator-norm budget, one in the trial value and one
in the escaping lower bound.

The zero-margin boundary is already realized inside the same carrier. In the
weak-coupling range of (55.18b), $m=\epsilon_*$ and the radial strings there
are weakly null normalized near-minimizers. Thus no positive uniform radius
depending only on $\epsilon_*-m$ can be asserted at equality; at $w=0$ itself
there need not be a normalized ground state. This is a sharp boundary for
the *gap-based certificate*. It does not claim that every individual
perturbation at equality destroys every possible threshold state, nor that
the sufficient radius is necessary for a fixed perturbation.

The result is a stability statement for the declared occurrence operator.
It does not turn bounded multiplication into a native FIB action, does not
identify $\epsilon_*-m$ with a physical noise budget, and does not establish
an operation-, metric-, field- or clock-preserving bridge to Euclidean space.
In particular it supplies no dimension-selection theorem; it records how a
strict escape gap can be spent while retaining a normalized boundary state.

## 147.99 追加锚（本行以下为增补区）
## 148. Native coherent Markov lifts do not select a global heat-trace dimension

**Definition 148.1 (first births and the common birth Hilbert space).**
Fix one finite source $u\in\mathcal T$ of Definition 127.1 and its uncapped
accepted history. Put

$$
b_e=|\mathcal P_e|,\qquad |B_e|=2b_e,\qquad
\eta(u)=\min\{e\ge0:b_e>0\}.
\tag{148.1}
$$

Here $B_e$ is born in the step $e\to e+1$, rather than already being present
at epoch $e$. Every finite source has at least one terminal leaf, so
$\eta(u)=0$ if it has a beta leaf and $\eta(u)=1$ otherwise. The latter
initial step is an accepted empty birth. A beta always has a beta left
child, so $b_e>0$ at every $e\ge\eta(u)$; in particular there are infinitely
many nonempty birth blocks. This also follows from Proposition 128.3.
Its $h(u)$ additionally requires an existing branch: $\eta(\beta)=0$ and
$h(\beta)=1$, whereas $\eta(\alpha)=1$ and $h(\alpha)=2$. Thus the
first-birth offset below is $e-\eta(u)$, without dropping either singleton's
first birth or any accepted empty epoch.

Start with $G_0=I$ and $Q_0=-L_0$. Fix

$$
r>1,\qquad C>\max_{p\in V_0}s_0(p),\qquad
s_0(p)=-Q_0(p,p),\qquad C>0.
\tag{148.2}
$$

At every nonempty birth choose the parameters of Proposition 127.2 to be

$$
q_e=0,\qquad \lambda_e=C r^{e-\eta(u)},\qquad
K_e=\lambda_e I_{2b_e},\qquad
G_{e+1}=W_e^{-\mathsf T}
 \operatorname{diag}(G_e,\lambda_e^{-1}I_{2b_e})W_e^{-1}.
\tag{148.3}
$$

At an empty birth retain $G_{e+1}=G_e$, $Q_{e+1}=Q_e$ and the identity
embedding. The original $V_e,E_e,L_e,T_e$ and the initial norm are fixed;
the compatible successor norms are allowed to depend on $r$. The same
comparison parameter $t$ is used at every step, without an epoch-dependent
change of clock.

For each such lift write $S_e=G_e^{1/2}$,
$H_e=S_e^{-1}L_eS_e^{-1}$ and $V_e^{\rm iso}=S_{e+1}T_eS_e^{-1}$.
These $V_e^{\rm iso}$ are the normalized isometric embeddings called $V$
in Definition 135.1; they are not the occurrence sets $V_e$.
The common abstract birth space is

$$
\mathscr H_u=\mathbb C^{V_0}\mathbin{\oplus}
 \bigoplus_{e\ge\eta(u)}\mathbb C^{B_e}.
\tag{148.4}
$$

The finite initial summand includes all accepted empty steps before the
first birth. Identifications with the normalized finite spaces use the
orthogonal birth charts of Proposition 135.3. The dimensions and labels of
(148.4) are independent of $r$, although those identifications depend on
the chosen norms.

**Theorem 148.2 (a fixed beta source realizes every positive logarithmic heat dimension).**
For $u=\beta$, every $r>1$ and every $C>0$, (148.3) gives a conservative
Markov generator at every finite epoch, with exact form preservation, norm
preservation and same-clock intertwining as in (128.2). On
$\mathscr H_\beta$ their normalized inductive limit is the nonnegative
self-adjoint operator

$$
\begin{aligned}
H_r&=0_{\mathbb C}\mathbin{\oplus}
       \bigoplus_{e\ge0}C r^e I_{2F_{e+1}},\\
\operatorname{Dom}(H_r)
 &=\left\{(z_{\rm init},(z_e)_{e\ge0})\in\mathscr H_\beta:
       \sum_{e\ge0}(C r^e)^2\|z_e\|^2<\infty\right\},
\end{aligned}
\tag{148.5}
$$

where $z_{\rm init}$ is the initial scalar. This operator has compact
resolvent and a single zero
mode. With positive eigenvalues counted with multiplicity, put
$N_r^+(\Lambda)=\operatorname{Tr}\mathbf1_{(0,\Lambda]}(H_r)$. Then

$$
N_r^+(\Lambda)=
\begin{cases}
0,&0\le\Lambda<C,\\
2(F_{m+3}-1),&\Lambda\ge C,\quad
 m=\lfloor\log_r(\Lambda/C)\rfloor,
\end{cases}
\tag{148.6}
$$

and, writing $\varphi=(1+\sqrt5)/2$ and
$\gamma_r=\log\varphi/\log r$,

$$
\begin{aligned}
\operatorname{Tr}(e^{-tH_r})
 &=1+2\sum_{e\ge0}F_{e+1}e^{-tCr^e}<\infty\qquad(t>0),\\
\lim_{\Lambda\to\infty}
 \frac{\log N_r^+(\Lambda)}{\log\Lambda}
 &=\lim_{t\downarrow0}
 \frac{\log\operatorname{Tr}(e^{-tH_r})}{\log(1/t)}
 =\gamma_r.
\end{aligned}
\tag{148.7}
$$

Define $d_{\rm heat}=2\gamma_r$ for this global logarithmic Hilbert
heat-trace convention. For each prescribed real $d>0$, the choice
$r=\varphi^{2/d}$ gives $d_{\rm heat}=d$. In particular $d=3$ is attained
at $r=\varphi^{2/3}$, and is not selected by finite coherence and Markov
positivity.

**Proof.** First consider the finite construction for any source in
Definition 148.1. The initial generator is Markov. Formula (128.3) leaves
every old row, hence every old exit rate, unchanged. A child born at step
$j\to j+1$ has exit rate $\lambda_j$. Consequently, at a nonempty step
$e\to e+1$, an old parent's exit is either an initial exit rate or a
$\lambda_j$ with $j<e$. The strict growth in (148.3) and (148.2) imply

$$
\kappa_c:=\lambda_e-s_e(\operatorname{par}_e(c))>0,
\qquad
s_e(\operatorname{par}_e(c))+\kappa_c=\lambda_e.
\tag{148.8}
$$

Thus $K_e$ is exactly an allowed diagonal choice in Proposition 128.2,
not an arbitrary SPD block whose Markov signs were left unchecked.
Corollary 127.3 gives its actual generator, and Proposition 128.2 proves
nonnegative off-diagonal entries and zero row sums. Proposition 127.2 and
Theorem 128.1 give the inherited SPD metric and all four identities in
(128.2). Empty births have their identity extensions. This induction
constructs compatible prefixes of every finite length, without a future
choice changing any earlier metric or rate.

Proposition 135.3 now identifies the successor operator, unitarily and with
its old isometric copy, with $H_e\oplus\lambda_e I_{2b_e}$. Iterating these
identifications yields (148.4) and the diagonal direct-sum operator
$H_{\rm initial}\oplus\bigoplus_e\lambda_e I_{2b_e}$, where
$H_{\rm initial}=L_0$. The algebraic sum of the finite spaces is a core:
truncation converges both in norm and in the graph norm specified by
$\sum_e\lambda_e^2\|z_e\|^2$. Coordinatewise adjoints give exactly this
domain, so the operator is self-adjoint. Each block is finite-dimensional
and $\lambda_e\to\infty$. The resolvent $(H_r+I)^{-1}$ is therefore a norm
limit of finite-rank truncations, since its tail norm is at most
$\sup_{e\ge E}(1+\lambda_e)^{-1}\to0$. This proves compact resolvent.

For beta, the initial space has one vertex and zero form. The terminal
counts obey $a_{e+1}=b_e$, $b_{e+1}=a_e+b_e$, with $(a_0,b_0)=(0,1)$.
Hence $b_e=F_{e+1}$ for $F_0=0,F_1=1$, and (148.5) follows. Births at
$e=0,\ldots,m$ are precisely the blocks with eigenvalue at most $\Lambda$
when $m$ is as in (148.6). The finite identity
$\sum_{e=0}^mF_{e+1}=F_{m+3}-1$ proves the exact count, including equality
at $\Lambda=Cr^m$. There are no positive initial eigenvalues.

The Fibonacci formula gives $F_{m+3}-1\asymp\varphi^m$ for $m\ge0$.
Since $r^m\le\Lambda/C<r^{m+1}$ and
$\varphi^m=(r^m)^{\gamma_r}$, there are constants $a_-,a_+>0$, independent
of $\Lambda$, such that

$$
a_-(\Lambda/C)^{\gamma_r}
 \le N_r^+(\Lambda)
 \le a_+(\Lambda/C)^{\gamma_r}\qquad(\Lambda\ge C).
\tag{148.9}
$$

Taking logarithms proves the counting limit. Put
$Z_r^+(t)=\operatorname{Tr}(e^{-tH_r})-1$. The elementary identity
$e^{-t\lambda}=t\int_\lambda^\infty e^{-tx}\,dx$, summed over positive
eigenvalues with nonnegative integrands, gives

$$
Z_r^+(t)=t\int_0^\infty e^{-tx}N_r^+(x)\,dx.
\tag{148.10}
$$

This same intermediate identity is used for the different fixed operator
in [*FIB atomic biased boundary spectral counting*, Theorem 3.1](FIB_ATOM_BIASED_BOUNDARY_SPECTRAL_COUNTING.md).
Here (148.9) gives, for $0<t\le C^{-1}$,

$$
\frac{a_-}{\mathrm e}(Ct)^{-\gamma_r}
 \le \mathrm e^{-1}N_r^+(1/t)
 \le Z_r^+(t)
 \le a_+(Ct)^{-\gamma_r}
        \int_0^\infty e^{-x}x^{\gamma_r}\,dx.
\tag{148.11}
$$

The lower estimate counts the eigenvalues at most $1/t$; the upper
estimate substitutes (148.9) in (148.10), with the count zero below $C$.
The last integral is finite because $\gamma_r>0$. The same upper bound
also proves finiteness for every $t>0$. Taking logarithms in (148.11), and
then including the single zero mode, proves (148.7). Substitution of
$r=\varphi^{2/d}$ proves the claimed range. These bounds assert a
logarithmic exponent, without an exact Weyl coefficient or a limit of a
logarithmic derivative of the trace. $\square$

**Proposition 148.3 (separate full-source birth-count variant).**
For every fixed finite $u\in\mathcal T$, let $a(u),b(u)$ be its original
alpha- and beta-leaf counts. In the construction (148.2)--(148.4),

$$
b_e=a(u)F_e+b(u)F_{e+1},\qquad
H_{u,r}=L_0\mathbin{\oplus}
 \bigoplus_{e\ge\eta(u)}Cr^{e-\eta(u)}I_{2b_e}.
\tag{148.12}
$$

Its domain is $\sum_{e\ge\eta(u)}(Cr^{e-\eta(u)})^2\|z_e\|^2<\infty$
inside $\mathscr H_u$, with no additional restriction on the finite initial
component. It is self-adjoint with compact resolvent. For $\Lambda\ge C$,

$$
\begin{aligned}
N_{u,r}^+(\Lambda)
 &=N_{\rm initial}^+(\Lambda)
   +2\sum_{e=\eta(u)}^{\eta(u)+m}b_e,
 &m&=\lfloor\log_r(\Lambda/C)\rfloor,\\
\operatorname{Tr}(e^{-tH_{u,r}})
 &=\operatorname{Tr}(e^{-tL_0})
   +2\sum_{e\ge\eta(u)}b_e e^{-tCr^{e-\eta(u)}}.
\end{aligned}
\tag{148.13}
$$

Here $N_{\rm initial}^+(\Lambda)$ counts the positive eigenvalues of $L_0$
up to and including $\Lambda$, and the heat identity is for $t>0$.
Below $C$ only the initial positive count remains. The two logarithmic limits
displayed in (148.7) equal $\log\varphi/\log r$ for this fixed $u$ as well.

**Proof.** The terminal recurrence in the preceding proof gives the first
formula of (148.12), including $e=0$. It is also the birth-count identity
of IV, Theorem 112.4, now with the full source convention of Definition
127.1. The construction and direct-sum argument in Theorem 148.2 already
apply to these sources, proving the operator, domain and compactness
claims. Since $a(u)+b(u)>0$, the leading Fibonacci coefficient is positive:
$b_{\eta(u)+j}\asymp_u\varphi^j$ as $j\to\infty$. The cumulative sum
therefore has this same order. Counting blocks proves (148.13), and the
two-sided power and integral bounds of (148.9)--(148.11) apply with
source-dependent constants. The finite initial count and finite initial
heat trace do not change either logarithmic limit. All constants refer to
one fixed source; no uniformity over unbounded initial source sizes is
needed. $\square$

**Proposition 148.4 (constant-rate and uniformly bounded-exit boundaries).**
For the same sources, replacing $r>1$ by $r=1$ in (148.3), with $C$ as in
(148.2), still gives coherent conservative finite Markov generators, but

$$
H_{u,1}=L_0\mathbin{\oplus}\bigoplus_{e\ge\eta(u)}C I_{2b_e},
\qquad
\operatorname{Tr}\!\left(e^{-tH_{u,1}}
              \mathbf1_{(0,\infty)}(H_{u,1})\right)=\infty
\quad(t>0).
\tag{148.14}
$$

More generally, suppose a coherent family of finite lifts with the
normalized isometric embeddings of §135 has conservative Markov $Q_e$ and
a uniform exit bound $-Q_e(p,p)\le M<\infty$ over all its epochs and
vertices. If its Hilbert inductive limit is infinite-dimensional, the
compatible normalized operator extends to a bounded nonnegative
self-adjoint operator with spectrum in $[0,2M]$. Its full heat trace is
infinite at every positive time.

**Proof.** For $r=1$ every inherited exit is at most $C$, and
$K_e=C I_{2b_e}\succ0$. The actual-coordinate formula (128.3) has child
exit $C$ and child-to-parent rate $C-s_e(p)\ge0$, with the other entries
as in (128.4). Some of these parent rates are zero: this boundary uses
the displayed sign calculation, rather than asserting the strict
$\kappa_c>0$ hypothesis of Proposition 128.2. Coherence still follows
from Proposition 127.2 and Theorem 128.1. Proposition 135.3 gives
(148.14). Infinitely many positive modes contribute the same positive
number $e^{-tC}$ to that trace.

For the general comparison, each row of $-Q_e$ has diagonal $s_e(p)$ and
sum of absolute off-diagonal entries $s_e(p)\le M$. Gershgorin's bound
puts every real eigenvalue in $[0,2M]$. The eigenvalues are real and
nonnegative because $-Q_e$ is similar to the symmetric nonnegative $H_e$.
Thus $0\le H_e\le2MI$ in each normalized Hilbert space. Exact intertwining
makes these operators consistent on their dense isometric union, where
they have the same norm bound. Their extension is bounded self-adjoint
and satisfies $0\le H\le2MI$. Functional calculus gives
$e^{-tH}\ge e^{-2Mt}I$, whose trace is infinite in infinite dimension.
This comparison needs the uniform bound and compatible Hilbert structure;
finite Markov conservation alone does not impose either a heat-trace
exponent or trace finiteness. $\square$

**Definition 148.5 (scope of nonselection and the missing realization bridge).**
Here $d_{\rm heat}$ is twice a global logarithmic Hilbert heat-trace
exponent for the declared comparison operator. It is not a volume-growth
dimension, walk dimension, pointwise return exponent, spatial or manifold
dimension, or an identification of $t$ with physical time. The finite
Markov property refers to $Q_e$ in actual occurrence coordinates; an SPD
state metric need not be a diagonal measure, and its principal-root
normalization is not by itself a spatial heat-kernel realization.

The nonselection quantifier is already one fixed source $u=\beta$, the
same accepted substitutions, original unit-edge forms, parent-copy maps,
initial norm and comparison clock, with different allowed successor norms.
It does not hold a complete prescribed norm family fixed while varying its
spectrum. The parameter $r$ chooses external compatible metrics; it is not
a native executable control. In particular the theorem supplies no rule
making a native history choose $r=\varphi^{2/3}$. The freedom established
here concerns spectral realization, not removal of the information-escape
conditions of §129 or a physical consequence of the stability result in
§147. Deriving physical $d=3$ would additionally require a specified
metric, measure and locality/transport correspondence, a relation between
its heat law and physical observations, and a criterion selecting the
allowed norm or rate law. Such correspondences are extra hypotheses to be
proved for a proposed realization; they are not consequences of the birth
count.

The fixed biased boundary form in
[*FIB atomic biased boundary spectral counting*, Definitions 1.1 and 4.1,
Theorem 3.1](FIB_ATOM_BIASED_BOUNDARY_SPECTRAL_COUNTING.md) has its own
logarithmic exponent one, with its declared boundary measure and clock.
That conclusion is retained: no unitary, form, measure or clock
identification between that boundary operator and this family is assumed.
Hierarchical pure-point spectra have classical precedents, for example
Bendikov--Grigor'yan--Pittet--Woess,
[*Isotropic Markov semigroups on ultra-metric spaces*, §3.2,
Theorem 3.8](https://arxiv.org/html/1304.6271v3). That theorem supplies
context for hierarchical eigenfunction decompositions, not a native FIB
realization bridge. The repo-derived content here is the explicit
simultaneous Markov/coherence construction on these actual source births
and its range of global exponents; no originality or priority claim about
hierarchical spectral freedom is included.

## 148.99 追加锚（本行以下为增补区）
