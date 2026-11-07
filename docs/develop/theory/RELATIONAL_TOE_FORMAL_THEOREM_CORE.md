# Formal core for the relational TOE program

This note isolates the part that can be stated and proved without assuming a complete physical TOE.

## 1. Relational records and admissibility

A finite relational record is

\[
r=(n,\phi,a_0,a_1,E,K),
\]

with order \(n\in\mathbb N\), phase \(\phi\in\mathbb R\), active amplitudes \(a_0,a_1\in\mathbb C\), finite relation edges \(E\), and a tested kernel \(K\).

Admissibility is a predicate \(\operatorname{Adm}(r)\). Its first finite clauses are

\[
|a_0|^2+|a_1|^2=1,
\qquad K\succeq0,
\qquad K_{ii}=1,
\]

plus orientation, successor-kernel, and product-kernel clauses when the record declares those structures. Keeping `Adm` as a predicate makes every later theorem conditional on the exact finite contract instead of silently assuming quantum structure.

## 2. Rule transformers and least closure

For \(i\in\{0,1,2,3,4,5\}\), let \(\operatorname{Prem}_i(r)\) be the prerequisite for rule \(R_i\), and let \(\operatorname{Next}_i(r,r')\) mean that \(r'\) is the record generated from \(r\). Define

\[
\Phi_i(S)=S\cup\{r'\mid\exists r\in S,
\operatorname{Prem}_i(r)\land\operatorname{Next}_i(r,r')\land\operatorname{Adm}(r')\}.
\]

A family \(T\) is closed when

\[
\operatorname{Closed}_R(T)\iff
\bigwedge_{i=0}^{5}\Phi_i(T)\subseteq T.
\]

The least closed family above \(S\) is

\[
\operatorname{Cl}_R(S)=\bigcap\{T\mid S\subseteq T\land\operatorname{Closed}_R(T)\}.
\]

### Theorem 1: closure-operator laws

For every seed family \(S\), \(\operatorname{Cl}_R\) is extensive, monotone, and idempotent:

\[
S\subseteq\operatorname{Cl}_R(S),
\]

\[
S\subseteq T\Longrightarrow
\operatorname{Cl}_R(S)\subseteq\operatorname{Cl}_R(T),
\]

\[
\operatorname{Cl}_R(\operatorname{Cl}_R(S))
=\operatorname{Cl}_R(S).
\]

Moreover,

\[
\operatorname{Closed}_R(S)\Longleftrightarrow
\operatorname{Cl}_R(S)=S,
\]

and if \(S\subseteq T\) with \(T\) closed, then

\[
\operatorname{Cl}_R(S)\subseteq T.
\]

### Proof

Every closed superset \(T\) of \(S\) contains \(S\), so their intersection contains \(S\). This proves extensivity.

If \(S\subseteq T\), every closed superset of \(T\) is also a closed superset of \(S\). Thus the family intersected for \(\operatorname{Cl}_R(T)\) is smaller, and its intersection is larger:

\[
\operatorname{Cl}_R(S)\subseteq\operatorname{Cl}_R(T).
\]

Intersections of closed families are closed because each \(\Phi_i\) is monotone and preserves inclusion. Hence \(\operatorname{Cl}_R(S)\) is closed. It is itself a closed superset of \(S\), so applying the least-closed construction again cannot enlarge it. Extensivity applied to \(\operatorname{Cl}_R(S)\) gives the reverse inclusion. Therefore idempotence holds.

If \(S\) is closed, then \(S\) is one of the closed supersets in the defining intersection, so \(\operatorname{Cl}_R(S)\subseteq S\); extensivity gives equality. Conversely, if \(\operatorname{Cl}_R(S)=S\), the left side is closed, so \(S\) is closed.

Finally, if \(T\) is closed and contains \(S\), then \(T\) belongs to the family defining \(\operatorname{Cl}_R(S)\). The intersection is therefore contained in \(T\). ∎

The one-step generator \(\Phi=\bigcup_i\Phi_i\) is generally not idempotent. The closure operator is its saturation, not the one-step map itself.

## 3. Finite counterexample witnesses

A rule witness is

\[
\operatorname{Witness}_i(r,r')\Longleftrightarrow
\operatorname{Prem}_i(r)\land
\operatorname{Next}_i(r,r')\land
\neg\operatorname{Adm}(r').
\]

Witness soundness says that a declared failed extension is not admissible in the current closure. Witness completeness is a separate theorem and requires a finite test-basis assumption:

\[
r\notin\operatorname{Cl}_R(S)
\Longrightarrow
\exists i,w\;\operatorname{Witness}_i(w).
\]

This implication cannot be obtained from the abstract closure definition alone.

## 4. Recorded clock as a monoid cocycle

Let `Event` be a type, `History := List Event`, and let \(\omega:\mathrm{Event}\to\mathbb R_{\ge0}\). Define

\[
\tau(h)=\sum_{e\in h}\omega(e).
\]

### Theorem 2: clock additivity and prefix monotonicity

For histories \(h_1,h_2\),

\[
\tau(h_2++h_1)=\tau(h_2)+\tau(h_1).
\]

If \(h_1\) is a prefix of \(h_2\), then

\[
\tau(h_1)\leq\tau(h_2).
\]

If the suffix contains an event of positive weight, the inequality is strict.

### Proof

The additive law is `List.sum_append`. If \(h_2=h_1++t\), then

\[
\tau(h_2)=\tau(h_1)+\tau(t),
\]

and \(\tau(t)\ge0\). If one suffix event has positive weight, then \(\tau(t)>0\). ∎

Let \(A:\mathrm{History}\to U(\mathcal H)\) be a monoid action satisfying

\[
A(h_2++h_1)=A(h_2)A(h_1).
\]

If \(h^{-1}\) is a recorded inverse word with \(A(h^{-1})=A(h)^{-1}\), then

\[
A(h++h^{-1})=I,
\]

while positive event weights give

\[
\tau(h++h^{-1})>0.
\]

Thus state return and history return are distinct propositions.

## 5. Propagation kernel and static history

Let \(\mathcal H\) be a finite-dimensional Hilbert space and \(U_1,\ldots,U_N\) unitary. Let

\[
\mathcal K=\mathcal H^{N+1},
\qquad
D(x_0,\ldots,x_N)=
(x_1-U_1x_0,\ldots,x_N-U_Nx_{N-1}),
\]

and \(K=D^\dagger D\). Define \(W_0=I\), \(W_k=U_k\cdots U_1\), and

\[
V\psi=\frac1{\sqrt{N+1}}
\sum_{k=0}^{N}|k\rangle\otimes W_k\psi.
\]

### Theorem 3: static-history representation

\[
V^\dagger V=I,
\qquad
DV=0,
\qquad
K\succeq0,
\qquad
\ker K=\operatorname{ran}V.
\]

### Proof

Orthogonality of the clock basis and unitarity of each \(W_k\) give

\[
\langle V\psi,V\varphi\rangle
=\frac1{N+1}\sum_{k=0}^{N}
\langle W_k\psi,W_k\varphi\rangle
=\langle\psi,\varphi\rangle.
\]
Thus \(V^\dagger V=I\).

The \(k\)-th component of \(DV\psi\) is proportional to

\[
W_{k+1}\psi-U_{k+1}W_k\psi=0.
\]
Hence \(DV=0\).

For every \(x\),

\[
\langle x,Kx\rangle
=\langle x,D^\dagger Dx\rangle
=\|Dx\|^2\ge0,
\]
so \(K\succeq0\). If \(Kx=0\), positivity gives \(Dx=0\). Therefore

\[
x_{k+1}=U_{k+1}x_k,
\]

and induction yields \(x_k=W_kx_0\). Set \(\psi=\sqrt{N+1}x_0\). Then \(x=V\psi\), so \(\ker K\subseteq\operatorname{ran}V\). The reverse inclusion follows from \(DV=0\). ∎

## 6. Conditional clock readout

Let \(\rho\) be a density matrix on \(\mathcal H\), let \(P_k=|k\rangle\langle k|\otimes I\), and let \(E\) be an effect. For the static history state \(V\rho V^\dagger\),

\[
\operatorname{Tr}(P_kV\rho V^\dagger)=\frac1{N+1},
\]

and

\[
\operatorname{Tr}\left[(|k\rangle\langle k|\otimes E)V\rho V^\dagger\right]
=\frac1{N+1}\operatorname{Tr}(EW_k\rho W_k^\dagger).
\]

Therefore the conditional system state given clock result \(k\) is

\[
\rho_k=W_k\rho W_k^\dagger.
\]

### Proof

Use

\[
P_kV=\frac1{\sqrt{N+1}}|k\rangle\otimes W_k.
\]
Substitution and cyclicity of trace give both formulas. ∎

## 7. Discrete worldsheet closure

Let \(\Sigma\) be a finite connected simply connected two-complex. Assign a group element \(U_e\) to each oriented edge, with \(U_{e^{-1}}=U_e^{-1}\). If each face satisfies

\[
U_{\partial f}=I,
\]

then parallel transport between two vertices is independent of the chosen path.

### Proof

Two paths with the same endpoints form a closed loop. In a simply connected finite two-complex, every closed loop is generated by oriented face boundaries. Replacing a path by another therefore inserts products of \(U_{\partial f}\), each equal to the identity. The transport is path-independent. If \(U_{\partial f}\neq I\), the face carries a discrete curvature or holonomy witness. ∎

This theorem gives the rigorous discrete interface to a worldsheet. It does not derive a Polyakov action, Weyl anomaly cancellation, critical dimension, or a matter spectrum.
