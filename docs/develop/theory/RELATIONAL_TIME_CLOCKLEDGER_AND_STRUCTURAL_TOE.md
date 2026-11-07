# Relational time, ClockLedger, and the structural TOE boundary

## Status

This document specifies the temporal interface that connects the relational quantum automaton fixed point to OTF-001. It is a mathematical interface and implementation target. It does not claim a completed physical theory of everything.

The current relation automaton closes finite records with

\[
\Lambda_*=\Phi(\Lambda_*),\qquad \operatorname{Fail}(\Lambda_*)=\varnothing.
\]

That fixed point generates states, histories, gates, effects, instruments, joint records, and finite witnesses. It does not by itself define a physical scalar time. OTF-001 supplies the missing distinction between geometric change, geometric phase, and recorded time.

## 1. Three layers

The combined theory has three layers:

- **G, geometry:** directions, inner products, wedge products, rotations, paths, connections and holonomy;
- **Q, operations:** mixtures, positive effects, completely positive instruments, composition and joint kernels;
- **I, endogenous records:** observers, memory ports, history order, clocks and conditional readout.

Endogenous means represented inside the declared model. It does not mean that the representation is logically unique. Countermodel exclusion remains a separate obligation.

## 2. Three temporal quantities

For a direction path \(\gamma:\lambda\mapsto n(\lambda)\in S^2\), define the reversible change length

\[
q[\gamma]=\frac12\int_\gamma \|n'(\lambda)\|\,d\lambda.
\]

It is reparameterization invariant, additive under concatenation, and unchanged by path reversal. For a differentiable unitary path,

\[
\frac{dq}{dt}=\frac{\Delta H(t)}{\hbar}.
\]

This is a change functional. It is not a calibrated clock and it does not provide a time arrow.

The geometric phase is a separate field:

\[
A=i\langle\psi|d\psi\rangle,\qquad F=dA,\qquad \gamma_{\mathrm{geom}}=\oint A.
\]

A closed path can have positive \(q\) and nonzero phase while returning to the same direction. In particular, change length is reversal-even while the oriented phase is reversal-odd.

Recorded time is a third object. For declared events \(e_j\) with positive weights \(\omega(e_j)\),

\[
\tau_{\mathrm{rec}}(h)=\sum_{e_j\in h}\omega(e_j).
\]

An inverse gate can return the system state while leaving \(q>0\) and \(\tau_{\mathrm{rec}}\) increased. Therefore a state-only function \(T(n)\) cannot be a universal clock.

## 3. ClockLedger

Define the temporal ledger

\[
\mathsf{ClockLedger}
=(\mathsf H,\preceq_H,K_{\mathrm{prop}},\omega,\tau_{\mathrm{rec}},q,\gamma_{\mathrm{geom}},\Pi),
\]

where:

- \(\mathsf H\) is the finite history-prefix set;
- \(\preceq_H\) is the history order;
- \(K_{\mathrm{prop}}\) is the propagation residual;
- \(\omega\) assigns positive weights to recorded events;
- \(\tau_{\mathrm{rec}}\) is the record-time cocycle;
- \(q\) is the reversible path-change functional;
- \(\gamma_{\mathrm{geom}}\) is holonomy or geometric phase;
- \(\Pi_h\) is the conditional readout at history \(h\).

Clock consistency requires

\[
\tau(h_2\circ h_1)=\tau(h_2)+\tau(h_1),
\]

and

\[
h_1\preceq_H h_2
\Longrightarrow
\tau(h_2)\geq\tau(h_1).
\]

Strict increase is required for declared clock events. It is not required for every reversible gate.

## 4. Propagation closure and static histories

For a legal finite gate word

\[
W_k=U_k\cdots U_1,
\]

define

\[
D(x_0,\ldots,x_N)
=(x_1-U_1x_0,\ldots,x_N-U_Nx_{N-1}),
\qquad
K_{\mathrm{prop}}=D^\dagger D.
\]

Then \(K_{\mathrm{prop}}\succeq0\), and \(\ker K_{\mathrm{prop}}\) is exactly the space of histories satisfying every declared propagation relation.

The static-history embedding is

\[
V_{\mathrm{hist}}\psi
=\frac1{\sqrt{N+1}}
\sum_{k=0}^{N}|k\rangle_C\otimes W_k\psi.
\]

It lies in \(\ker K_{\mathrm{prop}}\), and conditional projection on \(|k\rangle_C\) returns \(W_k\psi\).

This is the temporal counterpart of the relation fixed point. The objects are different:

\[
\Lambda_*=\Phi(\Lambda_*)
\]

is a fixed family of admissible records, while

\[
K_{\mathrm{prop}}|\Omega_N\rangle=0
\]

is a zero-residual subspace of a chosen finite history. Their common principle is simultaneous satisfaction of all local relations.

## 5. Rule integration

The ClockLedger extends the six relational rules:

| Rule | Temporal interface |
| --- | --- |
| R0 identity and normalization | propagation residual remains positive and zero on legal histories |
| R1 binary distinction | clock events have distinguishable record ports |
| R2 oriented ternary closure | phase and history orientation are retained |
| R3 successor consistency | conditional readout agrees with the successor kernel |
| R4 complete positive readout | clock effects are positive and normalized |
| R5 independent composition | joint clocks and histories admit product kernels |

The finite visualizer may use a closure order as a display index. That index is not physical time until a ClockLedger and its cocycle have been constructed.

## 6. Candidate causal cone

For a Hermitian two-level element

\[
X=x_0I+x\cdot\sigma,
\]

the determinant is

\[
\det X=x_0^2-\|x\|^2.
\]

The positive cone satisfies

\[
x_0\geq0,\qquad x_0^2-\|x\|^2\geq0,
\]

and \(SL(2,\mathbb C)\) conjugation preserves the determinant and the positive cone. The clock cocycle can select the future orientation, while the relation vector supplies the spatial coordinates.

This is an algebraic causal-cone interface. It does not yet prove a physical Lorentzian manifold, local events, Einstein dynamics, or an energy-momentum interpretation.

## 7. Structural TOE tuple

The combined closure object is

\[
\Theta_{\mathrm{TOE}}
=(\Lambda,\Phi,\mathsf{ClockLedger},g,\nabla,A,\mathcal S,\mathsf{Obs},\otimes).
\]

The intended closure obligations are:

- **C1, relational fixed point:** \(\Phi(\Lambda)=\Lambda\) and \(\operatorname{Fail}(\Lambda)=\varnothing\);
- **C2, clock cocycle:** recorded time is additive, history-monotone, and not erased by inverse gates;
- **C3, metric and connection:** the kernel-induced metric, complex structure, connection and curvature are compatible;
- **C4, dynamics:** stationary closure-preserving paths of an action or Hamiltonian generate the legal successor family;
- **C5, observation:** all declared observation maps are complete positive readouts inside the ledger;
- **C6, composition:** independent histories have joint kernels and tensor-compatible effects;
- **C7, classical calibration:** a coarse-graining gives a classical or low-curvature limit and maps ledger units to seconds, distance and energy;
- **C8, counterexample feedback:** every finite witness has a dependency cone and a defined refinement operation.

The current project has finite slices of C1, C5 and C6, and OTF-001 has a finite C2 static-clock construction plus partial C3 algebraic bridges. C4, Lorentzian and Einstein dynamics, matter and gauge spectra, physical units, C7 and C8 remain open.

## 8. Implementation targets

The next formal files should reuse the existing closure-operator and fixed-point interfaces:

- `D5/S3/Quantum/Automaton/RelationalAutomatonClosure.lean`;
- `D5/S3/Quantum/Automaton/ClockLedger.lean`;
- `D5/S3/Quantum/Automaton/PropagationKernel.lean`;
- `D5/S3/Quantum/Automaton/CounterexampleRefinement.lean`.

The minimum ClockLedger declarations are

\[
\begin{aligned}
&\operatorname{clockAdditive},\qquad
\operatorname{clockMonotone},\\
&\operatorname{propagationResidual},\qquad
\operatorname{conditionalReadout},\\
&\operatorname{inversePreservesState},\qquad
\operatorname{inversePreservesHistory}.
\end{aligned}
\]

The finite experiment should emit the history-prefix set, propagation residuals, \(q\), geometric phase, \(\tau_{\mathrm{rec}}\), conditional readout, `clock_consistent`, `propagation_fixed_point`, and `fixed_point`.

A successful finite clock trace should demonstrate

\[
U_2=U_1^\dagger
\Longrightarrow
\rho_2=\rho_0,
\qquad
q>0,
\qquad
\tau_{\mathrm{rec}}(h_2)>\tau_{\mathrm{rec}}(h_0).
\]

## 9. Boundary statement

The combined RQA and OTF program is a structural or mathematical pre-TOE. It gives one fixed-point language for relation generation, quantum readout, gates and instruments, internal records, static global histories, conditional evolution, geometric change, phase holonomy, and candidate causal cones.

A completed physical TOE would additionally derive, from the same closed object, a Lorentzian metric, causal propagation, an action or Hamiltonian, Einstein and gauge dynamics, matter representations, masses, physical units, a classical limit, and falsifiable deviations or confirmations. Those results are not contained in the current finite closure and remain explicit research obligations.
