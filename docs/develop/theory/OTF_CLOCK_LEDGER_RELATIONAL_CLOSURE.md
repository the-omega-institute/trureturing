
# OTF ClockLedger: intrinsic time as a closed history interface

## Status and scope

This document connects the OTF-001 finite internal-clock construction to the relational quantum automaton and its fixed-point closure.

It is a mathematical interface and implementation target. It does not claim that physical spacetime, gravity, mass, particle statistics, or a complete Theory of Everything have already been derived.

The key separation is:

1. **change length** measures how much a relation has changed;
2. **geometric phase** measures oriented holonomy of a closed path;
3. **record time** measures ordered events retained by an internal ledger.

These quantities cannot be replaced by one state-only scalar without losing information.

## 1. ClockLedger

For a finite relational history system define

\[
\mathsf{ClockLedger}
=
(\mathsf H,\preceq,K_{\mathrm{prop}},\omega,\tau_{\mathrm{rec}},q,\gamma,\Pi).
\]

The components are:

- \(\mathsf H\): finite histories;
- \(\preceq\): the prefix relation on histories;
- \(K_{\mathrm{prop}}\): the positive propagation residual;
- \(\omega\): positive weights on declared record events;
- \(\tau_{\mathrm{rec}}\): cumulative record time;
- \(q\): reparameterization-invariant relational change length;
- \(\gamma\): geometric phase or holonomy;
- \(\Pi_h\): conditional readout at history \(h\).

A history is not just a state. It contains a state record, a gate prefix, retained event records, and the predecessor relation needed to reconstruct how the record was produced.

The minimal history record is

\[
h=(\rho_h,W_h,\mathsf E_h,\mathsf M_h,\operatorname{Pred}(h)),
\]

where \(\rho_h\) is the current relation state, \(W_h\) is the legal gate prefix, \(\mathsf E_h\) is the event ledger, \(\mathsf M_h\) is the retained memory record, and \(\operatorname{Pred}(h)\) is its causal predecessor set.

## 2. OTF propagation kernel

For a finite gate sequence \(U_1,\ldots,U_N\), define

\[
W_0=I,\qquad W_k=U_k\cdots U_1.
\]

For a history vector \(x=(x_0,\ldots,x_N)\), define the propagation difference

\[
D_{\mathrm{prop}}x
=
(x_1-U_1x_0,\ldots,x_N-U_Nx_{N-1}),
\]

and the residual

\[
K_{\mathrm{prop}}
=
D_{\mathrm{prop}}^\dagger D_{\mathrm{prop}}.
\]

Then

\[
\langle x,K_{\mathrm{prop}}x\rangle
=
\|D_{\mathrm{prop}}x\|^2\geq0.
\]

The propagation closure condition is

\[
K_{\mathrm{prop}}x=0.
\]

This is the time analogue of the relational automaton's positive-kernel closure. Every edge in the history graph contributes a local residual. A valid static history is a zero-residual global record.

For a source state \(\psi_0\),

\[
V_{\mathrm{hist}}\psi_0
=
\frac{1}{\sqrt{N+1}}
\sum_{k=0}^{N}
|k\rangle_{\mathrm C}\otimes W_k\psi_0
\]

lies in \(\ker K_{\mathrm{prop}}\). Conditional projection on the clock label \(k\) returns

\[
\Pi_k V_{\mathrm{hist}}\psi_0
\propto
W_k\psi_0.
\]

Therefore the same global state can be static with respect to the propagation constraint while its internal conditional records exhibit the prescribed reversible evolution.

## 3. Three different time quantities

### 3.1 Relational change length

For a direction path \(n(\lambda)\in S^2\), define

\[
q[\gamma]
=
\frac12\int_\gamma
\|n\wedge dn\|
=
\frac12\int
\|n'(\lambda)\|\,d\lambda.
\]

It has the properties

\[
q[\gamma_1\star\gamma_2]
=
q[\gamma_1]+q[\gamma_2],
\]

\[
q[\gamma^{-1}]=q[\gamma],
\]

\[
q[\gamma]=0
\Longleftrightarrow
\gamma\text{ is constant}.
\]

For pure-state paths this equals the Fubini-Study line length under the convention used by OTF-001. Along a differentiable unitary path,

\[
\frac{dq}{dt}
=
\frac{\Delta_\psi H(t)}{\hbar}.
\]

This is a change rate. It has no intrinsic time arrow because reversing the path leaves \(q\) unchanged.

### 3.2 Geometric phase

For a local normalized spinor \(\psi\), define

\[
A=i\langle\psi|d\psi\rangle,
\qquad
F=dA.
\]

Under \(\psi\mapsto e^{i\chi}\psi\),

\[
A\mapsto A-d\chi,
\qquad
F\mapsto F.
\]

For a closed direction loop,

\[
\gamma_{\mathrm{geom}}
=
-\frac{\Omega_{\mathrm{solid}}}{2}
\pmod{2\pi}.
\]

Reversing a loop keeps \(q\) fixed and changes the sign of \(\gamma_{\mathrm{geom}}\). Hence \(q\) and \(\gamma_{\mathrm{geom}}\) are independent ledger fields.

### 3.3 Record time

For a history with ordered events \(e_1,\ldots,e_k\), assign

\[
\omega(e_j)>0
\]

and define

\[
\tau_{\mathrm{rec}}(h)
=
\sum_{j=1}^{k}\omega(e_j).
\]

If a gate and its inverse return the system state,

\[
U_2=U_1^\dagger,
\qquad
U_2U_1=I,
\]

the state can return while the record time increases:

\[
\rho_{h\cdot U_1\cdot U_1^{-1}}
=
\rho_h,
\qquad
\tau_{\mathrm{rec}}(h\cdot U_1\cdot U_1^{-1})
>
\tau_{\mathrm{rec}}(h).
\]

This is the precise sense in which reversible gates and irreversible historical accumulation coexist.

## 4. Why a state-only clock fails

Suppose a scalar \(T(\rho)\) depends only on the current state and is required to increase on every nonconstant reversible path.

For a closed path \(\gamma\),

\[
\rho_{\gamma(0)}=\rho_{\gamma(1)},
\]

so

\[
T(\rho_{\gamma(1)})-T(\rho_{\gamma(0)})=0.
\]

If every segment had a strictly positive increment, additivity would require a positive total increment. This is a contradiction.

Therefore a global clock cannot be a function of the current state alone. It must depend on one or more of:

- history prefix;
- retained event records;
- causal order;
- an external or internal clock port;
- an explicitly declared irreversible record channel.

The relational automaton should therefore use

\[
\mathrm{Clock}:\mathsf H\to\mathbb R_{\geq0},
\]

rather than

\[
\mathrm{Clock}:\mathsf{St}\to\mathbb R_{\geq0}.
\]

## 5. ClockLedger closure obligations

A ClockLedger is closed when the following conditions hold.

### C0. Prefix order

If \(h\preceq h'\), then

\[
\tau_{\mathrm{rec}}(h')
\geq
\tau_{\mathrm{rec}}(h).
\]

The prefix relation is part of the model. It is not reconstructed from the current state.

### C1. Propagation closure

Every declared history obeys

\[
K_{\mathrm{prop}}h=0
\]

or carries a finite residual witness identifying the violated predecessor edge.

### C2. Conditional readout

For every history \(h\), the internal readout reproduces the declared gate prefix:

\[
\Pi_h(\rho_{\Omega})
=
W_h\rho_{\Omega}W_h^\dagger
\]

on the accessible port.

### C3. Reversal without erasure

A legal inverse gate may restore the active state, but it does not erase already declared records unless an explicit erasure channel is part of the protocol.

### C4. Change-length invariance

The relational change length satisfies reparameterization invariance and path concatenation:

\[
q[\gamma\circ f]=q[\gamma],
\qquad
q[\gamma_1\star\gamma_2]
=
q[\gamma_1]+q[\gamma_2].
\]

### C5. Holonomy compatibility

For a closed loop, the phase record is determined by the oriented connection and is invariant under local gauge changes:

\[
\gamma_{\mathrm{geom}}
\equiv
\oint_\gamma A
\pmod{2\pi}.
\]

### C6. Composition

For independent histories,

\[
h_{AB}=h_A\otimes h_B,
\]

and the joint propagation kernel must retain cross-relations. Marginal records alone do not satisfy composition closure.

### C7. Fixed point

If \(\Phi_{\mathrm{Clock}}\) is the rule generator that adds histories, gates, effects, clock records, and joint histories, then

\[
\Phi_{\mathrm{Clock}}(\Lambda)=\Lambda.
\]

A failed condition yields a finite witness with its dependency cone.

## 6. Integration with the relational quantum automaton

The existing six rules acquire a time interpretation:

| Automaton rule | ClockLedger interpretation |
|---|---|
| R0 identity and normalization | identity history and zero propagation residual |
| R1 binary distinction | first branch event in the history ledger |
| R2 oriented ternary closure | phase and holonomy-bearing relation record |
| R3 successor consistency | common propagation/successor kernel |
| R4 positive readout | conditional clock readout as a positive effect |
| R5 independent composition | tensor history with joint clock and cross-relations |

The fixed-point ledger is therefore

\[
\Lambda_{\mathrm{TOE}}
=
(\Lambda_{\mathrm{rel}},
\mathsf H,
K_{\mathrm{prop}},
\tau_{\mathrm{rec}},
q,
\gamma_{\mathrm{geom}},
\Pi,
\otimes).
\]

The current finite closure experiment supplies the first finite trace

\[
|S_0|=1\to |S_1|=3\to |S_2|=5\to |S_3|=6,
\qquad
S_4=S_3.
\]

The OTF extension adds a second trace:

\[
\Lambda_0
\subseteq
\Lambda_1
\subseteq
\Lambda_2
\subseteq\cdots
\]

where each round can add:

- a new history;
- a new propagation edge;
- a new conditional readout;
- a new event-clock value;
- a new holonomy record;
- a new joint composition.

A finite time closure is reached when no new admissible history or clock obligation is generated.

## 7. What this says about TOE

The combined framework has the architecture of a candidate TOE substrate:

1. a single relational state and history carrier;
2. quantum positivity and Born readout;
3. unitary gates as closed endomorphisms;
4. completely positive successor instruments;
5. tensor composition and joint correlations;
6. internal clocks and static-history representation;
7. geometric change length and phase holonomy;
8. a fixed-point rule generator with finite counterexamples.

It is not yet a physical Theory of Everything. The missing physical layers are:

- derivation of a nondegenerate four-dimensional Lorentz geometry;
- a dynamical action or Hamiltonian selected by the relational closure;
- gravity or a metric field equation;
- gauge fields and particle representations;
- physical units and the calibration of \(\hbar\), mass, distance, and clock rate;
- infinite-history and continuum limits;
- experimentally distinguishable predictions.

The correct claim is therefore:

\[
\text{relational quantum fixed point}
+
\text{ClockLedger}
=
\text{formal TOE architecture},
\]

while

\[
\text{formal TOE architecture}
\neq
\text{completed physical TOE}.
\]

## 8. Formalization target

The next Lean interface should reuse the existing closure operator and add:

    structure History where
      state : RelRecord
      prefix : List Gate
      events : List Event
      predecessors : Finset HistoryId

    structure ClockLedger where
      histories : Set History
      clockWeight : Event -> Real
      propagationResidual : History -> Real
      changeLength : History -> Real
      holonomy : History -> Real
      conditionalReadout : History -> Effect
      prefixMonotone : ...
      propagationClosed : ...
      readoutCompatible : ...
      fixedPoint : ...

The minimum theorems are:

    theorem clock_extensive :
      S ⊆ ClockClosure S

    theorem clock_monotone :
      S ⊆ T -> ClockClosure S ⊆ ClockClosure T

    theorem clock_idempotent :
      ClockClosure (ClockClosure S) = ClockClosure S

    theorem clock_closed_iff_fixed :
      ClockClosed S ↔ ClockClosure S = S

    theorem reversal_preserves_state_adds_history :
      state (h ++ [U, U⁻¹]) = state h
      ∧ tauRec (h ++ [U, U⁻¹]) > tauRec h

    theorem state_only_clock_impossible :
      ¬ ExistsGlobalStateOnlyMonotoneClock

The final theorem should be conditional:

> Every finite-rank ClockLedger fixed point with positive propagation kernel, compatible conditional readout, complete positive effects, and tensor-stable composition has the same minimal quantum representation as the corresponding relational fixed point. Time is represented by history order and record accumulation, while the static global state is represented by the propagation-kernel nullspace.

## 9. Boundary

OTF-001 gives a mathematically explicit finite internal-clock model. Its strongest contribution to the relational program is the separation of:

\[
q
\neq
\gamma_{\mathrm{geom}}
\neq
\tau_{\mathrm{rec}}.
\]

The first measures change, the second oriented holonomy, and the third retained historical order.

The current program becomes a candidate TOE architecture only when these fields are generated by the same fixed-point closure and can be tested by the same finite witness mechanism. Physical spacetime, gravity, matter, and particle dynamics remain additional closure layers.
