# Relational TOE: unified closure, ClockLedger, and worldsheet interface

## Status and scope

This is the single theory document for the relational quantum automaton and its structural TOE extension. It unifies the fixed-point closure, ClockLedger time layer, formal theorem core, and worldsheet/string interface.

It is a mathematical interface and paper-level theorem record. It does not claim that the complete physical TOE, full Lean kernel development, Lorentz/Einstein dynamics, string consistency, or matter spectrum have already been proved.

The current implementation and evidence are distributed across the companion visualization and experiment repositories. The theory itself is maintained in this one document and this one pull request.

## 1. Unified object

The theory has three internal layers:

- **G, geometry:** directions, inner products, wedge products, rotations, paths, connections, and holonomy;
- **Q, operations:** mixtures, positive effects, completely positive instruments, composition, and joint kernels;
- **I, records:** observers, memory ports, history order, clocks, conditional readout, and counterexample witnesses.

The unified closure object is

\[
\Theta_{\mathrm{TOE}}
=(\Lambda,\Phi,\mathsf{ClockLedger},g,\nabla,A,\mathcal S,\mathsf{Obs},\otimes).
\]

Here \(\Lambda\) is the relational ledger, \(\Phi\) its generation operator, \(\mathsf{ClockLedger}\) the temporal interface, \(g\) a candidate metric, \(\nabla\) a compatible connection, \(A\) a gauge or phase connection, \(\mathcal S\) a dynamical selection principle, \(\mathsf{Obs}\) the observation interface, and \(\otimes\) independent composition.

The complete closure target is

\[
\Phi(\Lambda)=\Lambda,
\qquad
\operatorname{Fail}(\Lambda)=\varnothing,
\qquad
\operatorname{Refine}(\Lambda,w)\text{ is defined for every finite witness }w,
\]
plus ClockLedger, metric, connection, action, observation, and composition compatibility.

## 2. Relational records and admissibility

A finite relational record is

\[
r=(n,\phi,a_0,a_1,E,K),
\]

with order \(n\in\mathbb N\), relative phase \(\phi\in\mathbb R\), active amplitudes \(a_0,a_1\in\mathbb C\), finite relation edges \(E\), and a tested kernel \(K\).

Admissibility is a predicate

\[
\operatorname{Adm}:\mathscr R\to\mathrm{Prop}.
\]

The first finite clauses are

\[
|a_0|^2+|a_1|^2=1,
\qquad
K\succeq0,
\qquad
K_{ii}=1,
\]

with orientation, successor, and product clauses added only when a record declares those structures. Keeping admissibility as a predicate prevents quantum conclusions from being silently inserted into the record type.

A finite failure witness is a tuple \((i,r,r')\) with

\[
\operatorname{Prem}_i(r)land
\operatorname{Next}_i(r,r')land
\neg\operatorname{Adm}(r').
\]

Witness completeness is a separate theorem. It does not follow from the abstract closure laws.

## 3. Six rule transformers and least closure

For \(i\in\{0,1,2,3,4,5\}\), define

\[
\Phi_i(S)=S\cup\{r'\mid
\exists r\in S,
\operatorname{Prem}_i(r)\land
\operatorname{Next}_i(r,r')\land
\operatorname{Adm}(r')\}.
\]

The combined one-step generation operator is

\[
\Phi(S)=\bigcup_{i=0}^{5}\Phi_i(S).
\]

The rules are:

| Rule | Generated obligation |
| --- | --- |
| R0 | identity and normalization |
| R1 | binary distinction |
| R2 | oriented ternary closure and phase |
| R3 | successor-kernel consistency |
| R4 | complete positive readout |
| R5 | independent-history composition |

A family \(T\) is closed when

\[
\operatorname{Closed}_R(T)
\Longleftrightarrow
\forall i,\ \Phi_i(T)\subseteq T.
\]

The least closed family above a seed \(S\) is

\[
\operatorname{Cl}_R(S)=
\bigcap\{T\subseteq\mathscr R\mid
S\subseteq T\land\operatorname{Closed}_R(T)\}.
\]

### Theorem 1: closure-operator laws

If every \(\Phi_i\) is monotone, then \(\operatorname{Cl}_R\) is extensive, monotone, and idempotent:

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
\operatorname{Closed}_R(S)
\Longleftrightarrow
\operatorname{Cl}_R(S)=S.
\]

### Proof

Every closed superset of \(S\) contains \(S\), so their intersection contains \(S\). This proves extensivity.

If \(S\subseteq T\), every closed superset of \(T\) is a closed superset of \(S\). The family intersected for \(T\) is therefore smaller, and its intersection is larger. Hence \(\operatorname{Cl}_R(S)\subseteq\operatorname{Cl}_R(T)\).

Intersections of closed families are closed by monotonicity of each \(\Phi_i\). Therefore \(\operatorname{Cl}_R(S)\) is itself closed. Applying the least-closed construction again adds nothing. Extensivity gives the reverse inclusion, proving idempotence.

If \(S\) is closed, it belongs to the family defining \(\operatorname{Cl}_R(S)\), so \(\operatorname{Cl}_R(S)\subseteq S\). Extensivity gives equality. Conversely, if \(\operatorname{Cl}_R(S)=S\), the left-hand side is closed, so \(S\) is closed. ∎

### Theorem 2: least fixed point above a seed

If \(\Phi\) is finitary and preserves directed unions, then

\[
S_0=S,
\qquad
S_{n+1}=\Phi(S_n),
\qquad
S_\omega=\bigcup_{n<\omega}S_n
\]

satisfies

\[
S_\omega=\operatorname{Cl}_R(S),
\qquad
\Phi(S_\omega)=S_\omega.
\]

### Proof

Extensivity gives an ascending chain. Directed-union preservation gives

\[
\Phi(S_\omega)
=\Phi\left(\bigcup_nS_n\right)
=\bigcup_n\Phi(S_n)
=\bigcup_nS_{n+1}
=S_\omega.
\]

Thus \(S_\omega\) is closed. If \(T\) is closed and \(S\subseteq T\), induction gives \(S_n\subseteq T\) for every \(n\), hence \(S_\omega\subseteq T\). Therefore it is the least closed family above \(S\). ∎

The finite experiment realizes the trace

\[
|S_0|=1,
\qquad
|S_1|=3,
\qquad
|S_2|=5,
\qquad
|S_3|=6,
\qquad
S_4=S_3.
\]

## 4. ClockLedger and recorded time

Let \((\mathsf H,\circ,e)\) be the free history monoid generated by declared events, with prefix order \(h_1\preceq_Hh_2\) when \(h_2=h_3\circ h_1\) for some \(h_3\). A ClockLedger is

\[
\mathsf{ClockLedger}
=(\mathsf H,\preceq_H,K_{\mathrm{prop}},\omega,
\tau_{\mathrm{rec}},q,\gamma_{\mathrm{geom}},\Pi).
\]

The quantities are distinct:

\[
q[\gamma]=\frac12\int_\gamma\|n'(\lambda)\|d\lambda,
\]

is a reversible geometric change length;

\[
A=i\langle\psi|d\psi\rangle,
\qquad
F=dA,
\qquad
\gamma_{\mathrm{geom}}=\oint A,
\]

is oriented phase holonomy; and

\[
\tau_{\mathrm{rec}}(h)=\sum_{e_j\in h}\omega(e_j),
\qquad
\omega(e_j)>0,
\]

is the history record time.

### Theorem 3: clock additivity and monotonicity

For histories \(h_1,h_2\),

\[
\tau(h_2\circ h_1)=\tau(h_2)+\tau(h_1).
\]

If \(h_1\preceq_H h_2\), then

\[
\tau(h_1)\leq\tau(h_2),
\]

with strict inequality whenever the suffix contains a positive-weight event.

### Proof

Write \(h_2=h_3\circ h_1\). Additivity gives \(\tau(h_2)=\tau(h_3)+\tau(h_1)\). Positivity gives \(\tau(h_3)\geq0\), with strict inequality when the suffix contains a positive event. ∎

If an inverse gate word returns the system state, the history need not return. Thus

\[
\rho_{h_2}=\rho_{h_1}
\quad\text{and}\quad
\tau(h_2)>\tau(h_1)
\]

can hold simultaneously.

## 5. Propagation kernel and static histories

Let \(\mathcal H\) be a finite-dimensional Hilbert space and \(U_1,\ldots,U_N\) unitary. Define

\[
W_0=I,
\qquad
W_k=U_k\cdots U_1,
\]

and

\[
D(x_0,\ldots,x_N)
=(x_1-U_1x_0,\ldots,x_N-U_Nx_{N-1}),
\qquad
K_{\mathrm{prop}}=D^\dagger D.
\]

### Theorem 4: propagation-kernel characterization

\[
\ker K_{\mathrm{prop}}=\ker D
=\{(x_0,W_1x_0,\ldots,W_Nx_0)\mid x_0\in\mathcal H\}.
\]

### Proof

For every \(x\),

\[
\langle x,K_{\mathrm{prop}}x\rangle
=\langle Dx,Dx\rangle
=\|Dx\|^2.
\]

Thus \(K_{\mathrm{prop}}x=0\) exactly when \(Dx=0\). The equations \(Dx=0\) are \(x_k=U_kx_{k-1}\), which recursively give \(x_k=W_kx_0\). ∎

### Theorem 5: static-history representation

Define

\[
V_{\mathrm{hist}}\psi
=\frac1{\sqrt{N+1}}
\sum_{k=0}^{N}|k\rangle_C\otimes W_k\psi.
\]

Then

\[
V_{\mathrm{hist}}^\dagger V_{\mathrm{hist}}=I,
\qquad
D V_{\mathrm{hist}}=0,
\qquad
\operatorname{ran}V_{\mathrm{hist}}=\ker K_{\mathrm{prop}}.
\]

### Proof

The \(k\)-th component of \(D V_{\mathrm{hist}}\psi\) is proportional to

\[
W_{k+1}\psi-U_{k+1}W_k\psi=0.
\]

Orthogonality of the clock basis and unitarity of \(W_k\) give

\[
\langle V_{\mathrm{hist}}\psi,V_{\mathrm{hist}}\varphi\rangle
=\frac1{N+1}\sum_{k=0}^{N}
\langle W_k\psi,W_k\varphi\rangle
=\langle\psi,\varphi\rangle.
\]

Every vector in the kernel is determined by its initial component, so the range is exactly the kernel. ∎

### Corollary: conditional clock readout

For \(P_k=|k\rangle\langle k|\otimes I\),

\[
\operatorname{Tr}(P_kV_{\mathrm{hist}}\rho V_{\mathrm{hist}}^\dagger)=\frac1{N+1},
\]

and the normalized conditional state is

\[
\rho_k=W_k\rho W_k^\dagger.
\]

## 6. Two-dimensional face closure

Let \(\Sigma\) be a finite connected simply-connected two-dimensional cell complex. Assign unitary transport \(U_e\) to each oriented edge, with \(U_{\bar e}=U_e^{-1}\). For a face \(f\) with oriented boundary \(e_1\cdots e_m\), define

\[
H_f=U_{e_m}\cdots U_{e_1}.
\]

### Theorem 6: flat face closure and path independence

If \(H_f=I\) for every face, transport between two vertices depends only on the endpoints. If some \(H_f\neq I\), path independence fails for paths whose difference contains that face.

### Proof

In a simply-connected finite cell complex, every closed loop is generated by oriented face boundaries and cancellation of adjacent inverse edges. Face holonomies equal to the identity and inverse-edge cancellation therefore make every closed-loop transport equal to the identity. Two paths with the same endpoints consequently have equal transport. Inserting a nontrivial face boundary changes transport by \(H_f\neq I\) without changing endpoints. ∎

This is the rigorous discrete worldsheet interface. It proves flat two-dimensional history consistency. It does not derive a Polyakov action, Weyl anomaly cancellation, critical dimension, or string spectrum.

## 7. Conditional quantum representation theorem

Assume that the least closed ledger has finite rank, all finite tested kernels are positive semidefinite, the active quotient carries a compatible complex structure \(J^2=-I\), legal gates preserve the kernel, complete readouts are positive, successor kernels agree, and independent products have joint kernels.

### Theorem 7: finite closed-ledger quantum representation

The radical quotient of the tested kernel has a minimal complex Hilbert representation. Kernel-preserving reversible gates act unitarily, complete readouts act as positive effects, successor branches act as completely positive instruments, and independent histories act by tensor-product composition. The representation is unique up to phase-preserving unitary gauge and hidden radical extensions.

### Proof outline and boundary

The positive kernel defines a pre-Hilbert history space. Quotienting by the radical and completing gives the GNS carrier. The orientation operator descends and supplies multiplication by the complex unit. Kernel-preserving reversible maps become isometries, hence unitaries in finite rank. Positive readouts are represented by effects through finite-dimensional Riesz representation. Successor-kernel equality makes branches linear; auxiliary-stable positivity gives complete positivity. Product-kernel equality gives the tensor Gram representation. Minimality follows from the radical quotient. This theorem is conditional and does not derive physical dynamics, worldsheet consistency, or a matter spectrum.

## 8. Structural TOE boundary

The proven theorem chain is

\[
\text{closure operator}
\longrightarrow
\text{least fixed point}
\longrightarrow
\text{ClockLedger}
\longrightarrow
\text{static history}
\longrightarrow
\text{flat face closure}
\longrightarrow
\text{conditional quantum representation}.
\]

The remaining theorem targets are:

- metric and connection reconstruction from the relation kernel;
- Lorentzian causal dynamics and Einstein equations;
- action or Hamiltonian selection;
- worldsheet action and quantum consistency;
- gauge and matter representations;
- mass, charge, units, and classical limit;
- witness completeness and counterexample refinement;
- falsifiable predictions.

The current theory is therefore a structural or mathematical pre-TOE. The formal core is proved at paper level, the finite fixed point is executable, and the remaining physics is recorded as explicit theorem targets rather than hidden assumptions.


## 10. Gravity closure and attraction

The current fixed point and ClockLedger provide the data needed to state a gravity interface. They do not yet determine a unique metric or field equation.

Define the gravity layer

\[
\mathsf{GravityClosure}
=
(\mathcal M,g,\mathsf{ClockLedger},\nabla,R,\mathcal S_{\mathrm{grav}},T),
\]

where \(\mathcal M\) is the reconstructed configuration manifold, \(g\) the candidate metric, \(\nabla\) a compatible connection, \(R\) its curvature, \(\mathcal S_{\mathrm{grav}}\) the closure-preserving dynamical action, and \(T\) the source record or stress response.

A candidate metric may be reconstructed from the relation kernel by a diagonal second variation, for example

\[
g_{ij}(x)
=
-\left.
\partial_i\partial_{j'}\log K(x,x')
\right|_{x=x'},
\]

or by a Bures/Fubini--Study second variation. This is a reconstruction interface. Nondegeneracy, Lorentzian signature, and physical units remain obligations.

### Conditional gravitational theorem

Assume:

1. the fixed ledger reconstructs a smooth Lorentzian metric \(g\);
2. the ClockLedger selects a future cone and proper relational parameter \(\tau\);
3. \(\nabla g=0\);
4. source-free histories extremize
   \[
   \mathcal S_{\mathrm{geo}}[x]
   =
   \frac12\int g_{\mu\nu}(x)\dot x^\mu\dot x^\nu\,d\tau;
   \]
5. observed records are invariant under the common coordinate representation.

Then free histories satisfy

\[
\ddot x^\mu+
\Gamma^\mu_{\alpha\beta}
\dot x^\alpha\dot x^\beta=0.
\]

The trajectory is universal because the action contains the metric and history parameter, not a species-dependent force coefficient. Neighboring histories satisfy

\[
\frac{D^2\xi^\mu}{D\tau^2}
=
-R^\mu{}_{\nu\alpha\beta}
u^\nu\xi^\alpha u^\beta.
\]

Therefore the invariant content of gravitational attraction is convergence or separation of neighboring legal histories under curvature. The Newtonian force language is a coordinate and weak-field limit.

### Proof

Varying the geodesic action gives

\[
\delta\mathcal S_{\mathrm{geo}}
=
-\int
\left(
\ddot x^\mu+
\Gamma^\mu_{\alpha\beta}
\dot x^\alpha\dot x^\beta
\right)
g_{\mu\nu}\delta x^\nu\,d\tau
\]

after integration by parts and using metric compatibility. Arbitrary compactly supported variations give the geodesic equation. Varying a one-parameter family of geodesics and commuting covariant derivatives gives the Jacobi equation above. ∎

In a static weak field with

\[
g_{00}=-(1+2\Phi/c^2),
\]

and slow spatial velocity, the geodesic equation reduces to

\[
\ddot{\mathbf x}=-\nabla\Phi.
\]

This is the conditional bridge from the relational metric to Newtonian attraction.

### No-go result for the current axioms

The present RQA and OTF closure clauses do not determine gravity uniquely. Let \(\Lambda_*\) and its ClockLedger satisfy all current finite closure rules. Pair them once with a flat metric \(g\), and once with a conformally curved metric

\[
g'_{\mu\nu}=e^{2f(x)}g_{\mu\nu}
\]

for a smooth nonconstant \(f\), while leaving the relation ledger and finite records unchanged. Without a metric-reconstruction axiom and a gravitational action, both extensions satisfy the current record-level closure but give different geodesics and curvature. Therefore attraction is not derivable from R0--R5 and ClockLedger alone.

### Additional gravity obligations

A unique gravity theory requires at least:

- **C9, metric reconstruction:** the relation kernel determines a nondegenerate metric;
- **C10, clocked causal cone:** ClockLedger selects the future orientation and Lorentzian cone;
- **C11, connection compatibility:** \(\nabla g=0\), \(\nabla J=0\), and face holonomy equals curvature;
- **C12, geodesic/action principle:** source-free legal histories are stationary paths;
- **C13, source law:** variation with respect to \(g\) gives
  \[
  \mathcal E_{\mu\nu}=\kappa T_{\mu\nu},
  \qquad
  \nabla^\mu\mathcal E_{\mu\nu}=0;
  \]
- **C14, Newtonian and classical calibration:** the weak-field limit fixes \(G\), clocks, distance, and energy.

The current theory provides the candidate data and the conditional theorem. It does not yet prove C9--C14.

### Relation to the worldsheet layer

A two-dimensional face closure may supply a worldsheet interface. If a worldsheet action and its quantum consistency conditions are added, target-space beta-function equations become a possible route to metric dynamics. This is a string-theoretic bridge, not a consequence of the current fixed-point theorem. The unified theory must therefore keep separate:

\[
\text{RQA fixed point}
\to
\text{ClockLedger}
\to
\text{candidate metric/connection}
\to
\text{worldsheet consistency}
\to
\text{gravity field equation}.
\]

## 11. Autonomous closure dynamics and generated constants

The finite H/S/X/Z experiment is a closure certificate, not yet an autonomous universe. Its gate alphabet, rule prerequisites, and admissibility tests are declared in advance. A self-evolving origin automaton must generate persistent cycles, promote stable invariants, and retain the records that make those invariants observable.

Define the autonomous ledger state

\[
X_n=(\Lambda_n,\mathsf H_n,\mathsf C_n,\mathsf{Const}_n,\mathsf{Law}_n),
\]

where \(\Lambda_n\) is the admissible relation family, \(\mathsf H_n\) its histories, \(\mathsf C_n\) clock candidates, \(\mathsf{Const}_n\) promoted invariants, and \(\mathsf{Law}_n\) relations stable across generated histories.

An autonomous update has the form

\[
X_{n+1}=\mathcal A(X_n)
=\operatorname{Cl}_R\Bigl(
X_n\cup\operatorname{Succ}(X_n)
\cup\operatorname{Cycle}(X_n)
\cup\operatorname{Promote}(X_n)
\cup\operatorname{Face}(X_n)
\Bigr),
\]

with admissibility and finite-witness feedback. A fixed point of \(\mathcal A\) must stop generating new states, clocks, constants, laws, and faces.

### Definition: primitive persistent cycle

A primitive cycle is a pair \((x,p)\) for which an autonomous successor \(F\) satisfies

\[
F^p x=x,
\qquad
0<q<p\Longrightarrow F^q x\neq x.
\]

A phase observable \(c:\mathsf H\to S^1\) has winding increment

\[
w=\frac{\widetilde c(F^p x)-\widetilde c(x)}{2\pi}\in\mathbb Z,
\]

where \(\widetilde c\) is a lift from the circle to its universal cover.

### Theorem: cycle-to-clock

Assume a primitive \(p\)-cycle, a history monoid generated by actual events, positive event weights \(\omega(e)>0\), an additive cocycle

\[
\tau(h_2\circ h_1)=\tau(h_2)+\tau(h_1),
\]

and a nonconstant periodic readout stable under gauge, refinement, and synchronization. Then

\[
\theta_k=\frac{2\pi k}{p}
\]

is a periodic phase coordinate and

\[
\tau_k=k\omega
\]

is an internal physical time on the cycle. Its period is

\[
T=p\omega.
\]

### Proof

The primitive cycle gives a faithful \(\mathbb Z_p\) action on the cycle. The additive cocycle is linear in the number of appended events, so \(\tau_k=k\omega\). The nonconstant readout excludes a constant state label and a pure gauge oscillation. Stability under refinement and synchronization makes the period and clock ratio invariant across the declared closure class. The cycle alone fixes only a dimensionless period and ratios. A physical unit requires calibration of \(\omega\). ∎

### No-go theorem: a state-only clock is impossible

Let \(F^p x=x\) be a nontrivial cycle. No function \(T:S\to\mathbb R\) can be strictly increasing along every successor step:

\[
T(Fx)>T(x)\Longrightarrow T(F^p x)>T(x),
\]

contradicting \(F^p x=x\). Therefore physical time must be history-dependent. The current closure round or visualizer step is an iteration index, not a physical clock.

The mathematical circle becomes physical time only when it has a primitive cycle, an unwrapped lift, a positive additive record cocycle, a stable nonconstant readout, observer synchronization, and unit calibration. Without these conditions it is only phase or holonomy.

### Generated constants and laws

A scalar or tensor \(\kappa\) is a generated constant when

\[
\kappa(\mathcal A X)=\kappa(X),
\]

and it is invariant under gauge, observer quotient, history reparameterization, and admissible coarse-graining. The candidate set is

\[
\operatorname{Const}(\mathcal A)=
\{\kappa\mid \kappa\circ\mathcal A=\kappa,\ \kappa\text{ stable and observable}\}.
\]

A generated law is an invariant relation \(L\) satisfying

\[
L(X)=0\Longrightarrow L(\mathcal A X)=0
\]

through the declared basin of the autonomous fixed point. Repeated numerical values are not automatically physical constants. They must survive gauge, refinement, observer and calibration tests.

The present H/S/X/Z trace does not yet satisfy this autonomous condition. It has a fixed gate set and fixed finite orbit. It proves declared closure, but does not discover gates, detect primitive cycles as clocks, promote constants, or derive laws.

### Clock-lapse bridge to gravity

If every spatial relation location carries a synchronized stable cycle, its calibrated rate can define a lapse \(N(x)\). A candidate coarse-grained metric is

\[
ds^2=-N(x)^2c^2dt^2+h_{ij}(x)dx^idx^j.
\]

For \(N\approx1+\Phi/c^2\), slow geodesics satisfy

\[
a^i\approx-c^2h^{ij}\partial_j\log N
\approx-h^{ij}\partial_j\Phi.
\]

This makes a spatial gradient of internal clock rate a candidate source of gravitational attraction. It still requires clock-to-lapse calibration and a source-to-lapse or action equation. The current theory does not derive either one.

The autonomous closure target is therefore

\[
\boxed{
\text{seed}
\to\text{successors}
\to\text{primitive cycles}
\to\text{clock lifts}
\to\text{stable constants}
\to\text{stable laws}
\to\text{new closure fixed point}
}
\]
