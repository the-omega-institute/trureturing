# Relational fixed points, world-sheets, and the string-theory boundary

## Status and scope

This document defines a candidate interface between the relational quantum automaton, OTF-001 internal time, and world-sheet theories. It is a structural bridge and an implementation target. It does not claim that string theory, critical dimension, gauge groups, or a physical target spacetime have already been derived.

The current theory has three related objects:

1. a fixed family of admissible relational records \(\Lambda_*\);
2. finite histories and a ClockLedger with propagation residual \(K_{\mathrm{prop}}\);
3. local direction geometry, phase holonomy, and positive quantum readout.

String theory requires a fourth object: a two-dimensional world-sheet with an action and quantum consistency conditions. The main purpose of this document is to specify exactly what must be added.

## 1. Worldline versus world-sheet

A finite RQA gate word

\[
W_k=U_k\cdots U_1
\]

is a one-parameter or discrete history. In geometric language it is a worldline-like record

\[
\gamma:h\longrightarrow \mathcal M,
\]

where \(h\) is a history prefix and \(\mathcal M\) is a candidate relation-state manifold. The OTF change length

\[
q[\gamma]=\frac12\int\|n'(\lambda)\|\,d\lambda
\]

belongs at this level.

A string world-sheet requires two independent parameters:

\[
\Sigma\ni \xi^a=(\tau,\sigma),
\qquad
X:\Sigma\longrightarrow \mathcal M.
\]

A fixed \(\sigma\) slice can be an RQA history in the ClockLedger, while \(\tau\) orders successor records. The second parameter is not automatically supplied by adding the word “time”. It requires a two-dimensional family of compatible histories and a local rule relating neighboring \(\sigma\)-slices.

The minimum relational world-sheet record is therefore

\[
\mathcal W=(\Sigma,h_{ab},X,\Lambda_*,\mathsf{ClockLedger},K_\Sigma),
\]

where \(h_{ab}\) is an auxiliary world-sheet metric and \(K_\Sigma\) tests the compatibility of all local cells and boundaries.

A one-dimensional ClockLedger is not yet a string world-sheet. The missing closure is the transverse \(\sigma\)-direction.

## 2. Candidate world-sheet action

If the fixed-point kernel induces a target metric \(g_{\mu\nu}\), a candidate reparameterization-invariant action is

\[
S_{\mathrm{ws}}[X,h]
=\frac{1}{4\pi\alpha'}
\int_\Sigma d^2\xi\,\sqrt h\,h^{ab}
 g_{\mu\nu}(X)\partial_aX^\mu\partial_bX^\nu.
\]

A phase or holonomy sector may supply a candidate two-form coupling

\[
S_B[X]
=\frac{1}{4\pi\alpha'}
\int_\Sigma d^2\xi\,\epsilon^{ab}
 B_{\mu\nu}(X)\partial_aX^\mu\partial_bX^\nu.
\]

A measure or record-density sector may supply a dilaton-like term

\[
S_\Phi[X,h]
=\frac{1}{4\pi}
\int_\Sigma d^2\xi\,\sqrt h\,\Phi(X)R^{(2)}(h).
\]

The combined candidate is

\[
S_{\mathrm{candidate}}=S_{\mathrm{ws}}+S_B+S_\Phi+S_{\mathrm{ledger}}.
\]

The first three terms have the standard world-sheet form. The new term \(S_{\mathrm{ledger}}\) would encode relational admissibility, propagation residuals, clock cocycles, and boundary records. It has not yet been derived from \(\Phi(\Lambda)\).

The current RQA and OTF theory can motivate the ingredients:

- \(g\) may be a second variation of the relational kernel, a Bures metric, or a Fubini--Study metric on an active quotient;
- \(B\) may arise from a transgressed phase or holonomy structure;
- \(\Phi\) may arise from a record measure or determinant factor;
- \(S_{\mathrm{ledger}}\) must enforce the fixed-point and ClockLedger constraints.

These are candidate identifications. The current theory has a one-form phase connection \(A\) and its curvature \(F=dA\). It does not yet prove that this \(A\) is a string target-space two-form \(B\). A worldline Berry connection and a world-sheet \(B\)-field have different degrees and require an explicit transgression map.

## 3. Relational kernel to target geometry

The current relation theory supplies positive kernels and local quantum metrics. A candidate target metric can be defined from a smooth kernel by

\[
g_{ij}(x)
=-\left.\partial_i\partial_{j'}\log K(x,x')\right|_{x=x'},
\]

or by the second variation of a Bures or Fubini--Study distance. The construction must prove:

1. independence from the chosen local representation;
2. nondegeneracy on the intended target directions;
3. compatibility with the complex structure \(J\);
4. invariance under the legal relation endomorphisms;
5. a coherent connection and curvature on overlaps.

OTF-001 currently gives a positive semidefinite direction metric of rank at most two for the map into \(S^2\). That is a local state-space metric, not yet a target-space metric for a string. It cannot by itself supply a nondegenerate Lorentzian spacetime.

The positive Hermitian cone gives a useful algebraic bridge:

\[
X=x_0I+x\cdot\sigma,
\qquad
\det X=x_0^2-\|x\|^2.
\]

The positive cone and \(SL(2,\mathbb C)\) conjugation provide a candidate causal-cone structure. A clock cocycle can select a future orientation. To become a target spacetime, the construction still needs events, locality, propagation, a nondegenerate metric, and a dynamical curvature law.

## 4. World-sheet closure conditions

A relational world-sheet should satisfy the following conditions.

### W1. Cell admissibility

Every finite world-sheet cell must have an admissible relational record. Its tested kernel is positive, its boundary records agree, and its local clock increments are compatible.

### W2. Slice compatibility

For each fixed \(\sigma\), the \(\tau\)-slice is a legal ClockLedger history. For each fixed \(\tau\), the \(\sigma\)-slice is a legal transverse relation. The two propagation orders must agree on overlaps.

### W3. Reparameterization closure

Changes of world-sheet coordinates must preserve the observable record and the action. This is stronger than the current RQA history-prefix invariance.

### W4. Local-to-global gluing

Records on adjacent cells must glue into a global kernel. Pairwise or triangular compatibility is insufficient if the global Gram rank or holonomy obstruction fails.

### W5. Boundary closure

For open histories, boundary ports must carry admissible records and boundary interactions. If a boundary gauge field is introduced, its relation to the fixed-point observation ports must be explicit.

### W6. Quantum world-sheet consistency

After quantization, the world-sheet theory must have a consistent measure, no uncancelled anomaly, and a well-defined physical state space. This condition cannot be replaced by finite RQA positivity.

## 5. Conformal consistency and critical dimension

A genuine string theory requires more than a classical world-sheet action. Quantum Weyl and diffeomorphism consistency impose beta-function or anomaly constraints. In schematic form,

\[
\beta^g=0,
\qquad
\beta^B=0,
\qquad
\beta^\Phi=0,
\]

along with cancellation of the total world-sheet central charge.

The RQA currently has no world-sheet central charge and no derived target dimension. Therefore neither the bosonic critical dimension nor a superstring critical dimension follows from the present closure. The three coordinates of the binary relation are Bloch or relational coordinates. They are not automatically the target dimension of a string.

A future derivation would need a world-sheet ledger whose quantum fluctuation count produces a central-charge balance:

\[
c_{\mathrm{matter}}+c_{\mathrm{ghost}}+c_{\mathrm{internal}}=0.
\]

Until such a theorem exists, critical dimension is an input or an external string-theory constraint, not a result of RQA.

## 6. Gauge fields, defects, and matter candidates

The fixed-point ledger naturally contains holonomy, residual fibres, and closed endomorphisms. These can supply candidates for gauge structure:

\[
A\in\Omega^1(\mathcal M,\mathfrak g),
\qquad
F_A=dA+A\wedge A.
\]

The current active structures include complex phase and local \(U(1)\)/\(SU(2)\) transport. The theory has not derived \(SU(3)\), the Lorentz group as a physical gauge sector, supersymmetry, anomaly cancellation, or the Standard Model representation content.

A possible matter dictionary is:

- stable local holonomy classes as excitations;
- nontrivial residual fibres as internal degrees of freedom;
- defect or homology classes as conserved charges;
- representation spectra of the closed endomorphism algebra as particle labels;
- action eigenvalues as candidate masses or energy scales.

These are candidate constructions. A particle interpretation requires a dynamical action, a Hilbert space of excitations, a stability theorem, a mass scale, and a map to measured charges.

## 7. Relation to open strings and boundaries

If a world-sheet has boundaries, boundary records are part of the relational automaton rather than external measurement devices. A boundary condition may be represented as a subledger

\[
\partial\Sigma\longrightarrow\mathsf{BoundaryRecord}(\Lambda_*).
\]

Open-string gauge fields would require a boundary coupling and a proof that boundary transformations act as legal fixed-point endomorphisms. The current RQA observation ports are a natural place to define this interface, but no open-string spectrum or D-brane category has been derived.

## 8. What is already unified and what is still open

The current chain is:

\[
\begin{aligned}
\Lambda_*&\longrightarrow \text{admissible relations and gates},\\
\mathsf{ClockLedger}&\longrightarrow \text{history order and internal time},\\
K_{\mathrm{prop}}&\longrightarrow \text{static global histories},\\
A,F&\longrightarrow \text{phase and holonomy},\\
g&\longrightarrow \text{candidate target geometry},\\
S_{\mathrm{candidate}}&\longrightarrow \text{candidate world-sheet dynamics}.
\end{aligned}
\]

Only the first four arrows have finite mathematical realizations in the current project. The fifth is a candidate metric interface, and the sixth is a proposed action layer. Conformal anomaly cancellation, critical dimension, gauge/matter spectra, and physical string observables remain open.

The exact classification is therefore:

- **RQA:** fixed-point generation of relational quantum structure;
- **OTF:** internal time, static histories, geometric change and observer records;
- **world-sheet bridge:** a candidate two-dimensional extension of the same closure;
- **string theory:** an additional quantum world-sheet consistency layer;
- **physical TOE:** requires target-space dynamics, fields, matter and empirical calibration.

The project is genuinely stitching these physical frameworks through a common closure language. It has not yet derived string theory from the fixed point. The next decisive theorem is a world-sheet closure theorem that constructs a two-dimensional history ledger, derives its action, and proves quantum consistency rather than merely importing the Polyakov form.
