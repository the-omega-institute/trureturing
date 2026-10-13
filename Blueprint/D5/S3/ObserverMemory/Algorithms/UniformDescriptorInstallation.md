# Uniform descriptor synthesis and literal-table transport

## Abstract

Uniform descriptor synthesis and literal-table transport.

This original uniform-descriptor application uses the supplied effective chart constructor, descriptor realization and complete target-row map. Every parameter tuple and epoch ranges over unbounded naturals. The native solver is pinned by the repository imports; solver correctness supplies no tractable complexity bound. The operational boundary is the already materialized finite table. Mathematical contracts are relative to the original presentation and reached-content rank assumptions.

**Definition 1.1 (Common descriptor query).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.descriptorQuery`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.descriptorQuery` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native bound tuple is exactly the disjoint descriptor layout of all read occurrences. The query is the original Total and Shared and Valid conjunction. Total universally quantifies every admitted original source; each H existentially quantifies that same source's epoch and phase data. No numeric coordinate or runtime cutoff is introduced.

**Definition 1.2 (Admitted source and terminal epoch query).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.haltQuery`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.haltQuery` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The common descriptor tuple remains free and fixed. Each chart query binds the complete source tuple followed by one terminal epoch using Fin.castAdd and Fin.natAdd; the actual haltAt formula retains its own phase witnesses. Native relabel laws identify these coordinates, rather than assumptions about the supplier's internal integer order.

**Definition 1.3 (An admitted original with a native run).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.ReachingSource`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.ReachingSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The certificate contains an original admitted source and a proof of a native run with the common literal realization. Proof fields are erased and do not appear in runtime state. No default original source or closure of the admitted family under update is required.

**Definition 1.4 (Guarded effective source extraction).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.chartSource`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.chartSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed NatPresburgerSolver supplies a source and epoch tuple. Its returned soundness proves admission before theta is evaluated. The exact native_support application proves reachability. The none branch invokes no source constructor.

**Definition 1.5 (All charts before default).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.sourceSearch`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.sourceSearch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite chart list is searched in order. A returned source is admitted and reaches the actual halt. The pinned List.findSome?_eq_none_iff law and the chart bijection establish that all-chart none is equivalent to no original source reaching that halt, including empty chart families.

**Definition 1.6 (Store the complete supplied target row).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.haltRow`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.haltRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A successful chart witness is sent once through theta and the task's effective complete target-row map. Shared compares all admitted original sources across all charts and independently chosen terminal epochs, identifying their entire target rows with this value. Every-chart none selects the complete supplied default row without fabricating a source.

**Definition 1.7 (Eager finite installed data).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.materialize`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.materialize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vector.ofFn computes every read literal and every instruction entry before returning the table. Read entries store permitted physical literal values and Vector successors; halt entries store full row values. Repeated physical literals are allowed at distinct occurrences while descriptor blocks remain distinct. Unreachable reads still require Valid; unreachable halts receive the complete default when all chart queries fail. The returned state type is exactly Fin of the candidate size and the initial state is the candidate start. Runtime program reads stored entries only; no solver, theta, descriptor realization, source advice, epoch counter, or witness is a runtime component.

**Definition 1.8 (Correctness at any actual halt endpoint).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.EndpointCorrect`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.EndpointCorrect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The property quantifies every original source and every halt-ended native run with its stored row. Its proof uses the successful run and native halt uniqueness with both endpoint halt instructions present. Arbitrary finite prefixes are not treated as unique.

**Definition 1.9 (Offline installation of one actual typed candidate).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.installCandidate`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.installCandidate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual descriptor query is solved using solveBounded. Returned soundness yields Valid and the exact original Total and Shared clauses. Literal realization is fixed before execution. No assumed termination, output recovery or arbitrary preloaded row correctness field is used.

**Theorem 1.10 (Returned installation succeeds).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.install_candidate_correct`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.install_candidate_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A returned installation equals materialize for one returned common valid tuple, terminates natively for every admitted original source, and stores the full target row at every actual halt endpoint. Exact size, start and entries are retained through the materialize equality. Feasibility alone never validates arbitrary preload data.

**Theorem 1.11 (Candidate feasibility returns an installation).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.install_candidate_exists_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.install_candidate_exists_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A candidate yields some installed table precisely when the common-descriptor Feasible property holds. The finite scan applies this contract at every complete typed candidate. The descriptor coordinates in Feasible remain unbounded.

**Theorem 1.12 (Exact candidate failure).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.install_candidate_none_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.install_candidate_none_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Returning none is equivalent to this candidate's infeasibility. The scan searches all sizes one through K and all initial states, instruction partitions, successors and type assignments. Its rejection excludes every successful original finite literal table by descriptor coverage and native run correspondence.

**Definition 1.13 (Complete tables with arbitrary state labels).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.LiteralTable`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.LiteralTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A table consists of a common initial state, a native instruction at every state, and an immutable complete row for each halt. Read addresses are permitted physical literals. Success quantifies every admitted original source and a finite halt-ended native run with the correct entire row. The representation retains unreachable entries. A finite state equivalence reindexes all instructions, read successors, update successors, rows and initial state; native run transport preserves both endpoint epochs.

**Definition 1.14 (The stored-table interpretation).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.literalTable`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.literalTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This interpretation reads the existing vector entries and full halt rows. It adds no mutable component, observation port or solver to the installed controller. It provides the arbitrary-label table view of a concrete installation.

**Definition 1.15 (Cover the complete physical installation).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.symbolicTable`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.symbolicTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every read instruction selects the type of its supplied covering descriptor. Every update successor, every read successor and every halt is retained. Type selection is independent of source and epoch; it also covers every unreachable read.

**Definition 1.16 (Occurrence-to-literal interpretation).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.physicalLiteral`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.physicalLiteral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each symbolic read occurrence is interpreted by the literal installed at that state in the original complete table. The map need not be injective. Its literal may differ from the presentation's chosen realization; membership in the supplied realization set is the required relation.

**Definition 1.17 (Numeric coordinates of a covered occurrence).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.coveredTuple`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.coveredTuple` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supplied descriptorOf and coverage provide one valid descriptor for each fixed physical literal. The same coordinates are used on every visit. The type equality identifies the numeric block with the selected type dimension. This reindexing belongs only to the proof of necessity.

**Definition 1.18 (One common descriptor valuation).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.coveredDelta`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.coveredDelta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The injective descriptorLayout extends the per-occurrence coordinates to one common finite tuple. No natural coordinate is bounded. This proof-only classical extension is separate from executable synthesis and is not retained in the returned table.

**Theorem 1.19 (Necessity for every complete literal table).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.successful_feasible`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.successful_feasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coverage gives valid descriptors and Real membership for all installed reads. Exact Reply makes chosen realizations and the original physical literals agree on every original source at every epoch. The arbitrary-address native transport theorem compares their runs without injectivity. Actual success supplies native Total; design_correct and phi_correct convert it to the original formula clause. For Shared, both independently chosen halt-ended runs are compared with the successful endpoints using run_halt_unique and both halt hypotheses. Their complete target rows equal the single preloaded row; exact Same supplies the formula. No installed-output-correctness premise is added.

**Theorem 1.20 (Necessity with arbitrary finite labels).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.successful_budget`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.successful_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonempty finite state type E, Fintype.equivFinOfCardEq gives an actual equivalence with Fin(card E). The proof transports the initial state, every instruction and successor, and all halt rows without deleting unreachable states. successful_feasible then supplies a true disjunct of the actual Psi sentence at the same cardinality. Reindexing uses classical choice only in proofs; the executable scan enumerates its finite candidates directly.

**Definition 1.21 (Original finite-controller existence).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.Solvable`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.Solvable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Solvable quantifies an arbitrary finite state type, a complete literal table on that type, its cardinality bound, and actual success on every original source. It is the original Solve_K proposition. It does not quantify one controller per source or impose a runtime bound.

**Definition 1.22 (Executable complete finite scan).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.synthesize`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.synthesize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

List.findSome? searches the actual candidates list and calls the native-solver-backed installCandidate on each candidate until an installation is returned. Complete enumeration covers sizes one through K, all initials and all entries, including unreachable entries and repeated literals. The candidate none contract and the pinned list-search law identify scan rejection with falsity of Psi. Therefore some exists exactly when Psi is true. Native original-table necessity and returned-table soundness identify this same truth value with Solvable. These applications use the original unbounded descriptor and source quantifiers. For K=0 the list is empty. Empty source families admit a one-state default halt when K is positive; the first returned candidate may instead be an update cycle because success on an empty family is vacuous.

**Theorem 1.23 (Soundness of the returned installation).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.synthesize_sound`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.synthesize_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A successful list search identifies a member of the actual complete candidate enumeration. install_candidate_correct identifies the returned eager table with materialize and supplies actual termination and complete output correctness. Candidate membership supplies its bound on counted states. Runtime reads stored physical literals and full rows; source constructors, chart tags, descriptor coordinates, phase witnesses, solver state and accumulators do not become controller components.

**Theorem 1.24 (Exact original rejection).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.synthesize_none_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.synthesize_none_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Returning none is equivalent to absence of every successful original literal table with at most K states on any finite labeling. Each candidate has no valid unbounded descriptor valuation satisfying Total and Shared. Conversely, a returned table yields an actual finite labeled successful table. Failure is a symbolic rejection of complete candidates and unbounded descriptor valuations, not failure of a fixed graph or a finite numeric search.

**Definition 1.25 (Original task correspondence).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.TaskCorrespondence`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.TaskCorrespondence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two raw tasks share physical permitted words, the entry epoch and complete row type. The supplied effective source equivalence compares rprime(Uprime^j(psi u),p) with r(U^j u,p) for every original u, every natural j and every permitted literal. Their complete targets agree under psi. No map is applied to U^j u, and no closure of the original family under update or arithmetic coordinate map is required.

**Definition 1.26 (Transfer the same literal table).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.installed`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.installed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The stored vector retains its exact size, start, read and update successors, physical words and full rows. Only the proof of literal permission changes. The transfer constructs finite stored data and introduces no runtime source-bijection state.

**Theorem 1.27 (Native run correspondence for raw tasks).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.corresponding_run`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.corresponding_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing arbitrary-address transport theorem identifies native runs of the same stored table under the original source equivalence. Initial and final control and epochs agree. The proof uses the supplied observation equality at each actual epoch; it does not assume that transport stays among original sources.

**Theorem 1.28 (Full-row success in both raw tasks).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.corresponding_successful`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.corresponding_successful` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source equivalence and exact native run correspondence transfer every actual halt and its entire installed row in both directions. No common halt epoch between two different sources is assumed. Applied to tables returned by either presentation, this proves success on the corresponding raw task.

**Theorem 1.29 (Equal synthesis truth under original task correspondence).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.corresponding_budget`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.corresponding_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two presentations may have different chart sets, source dimensions, admission formulas, descriptor types, descriptor dimensions and reached-content rank witnesses. A true first budget sentence yields an actual successful eager installation by the complete scan. The physical-word and complete-row correspondence transfers that installation; successful_budget covers every retained state and read occurrence in the second presentation and proves its budget sentence. The inverse original-source correspondence gives the reverse implication. The live construction uses exact native support for extraction and arbitrary-table necessity, and native halt uniqueness for Shared. It introduces no arithmetic coordinate map, source-domain closure, common source-dependent epoch or equality of the synthesized tables.

For two presentations of the same raw task, each Psi is equivalent to the same original Solvable proposition, so their truth values agree for every K. Each extracted table succeeds on that task. The presentations may use different chart sets, coordinate dimensions, admission formulas and rank witnesses. Under TaskCorrespondence, corresponding_successful transfers the literal table itself. The inverse source equivalence, reversed permission equivalence and entry equality, and observation and row equalities at the inverse source give the reverse task correspondence. Applying the same successful-table consequence in both directions gives equality of the two budget truth values. These implications assert existence and success; they assert neither equal synthesized tables nor comparable synthesis costs. The phase bound controls response-phase count only, and supplies no uniform action-duration bound.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.EndpointCorrect`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.LiteralTable`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.ReachingSource`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.Solvable`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.TaskCorrespondence`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.chartSource`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.corresponding_budget`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.corresponding_run`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.corresponding_successful`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.coveredDelta`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.coveredTuple`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.descriptorQuery`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.haltQuery`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.haltRow`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.installCandidate`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.install_candidate_correct`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.install_candidate_exists_iff`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.install_candidate_none_iff`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.installed`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.literalTable`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.materialize`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.physicalLiteral`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.sourceSearch`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.successful_budget`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.successful_feasible`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.symbolicTable`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.synthesize`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.synthesize_none_iff`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation.synthesize_sound`
- Dependency: [D5/S0/Computability/NatPresburgerSolver](../../../S0/Computability/NatPresburgerSolver.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign](UniformDescriptorDesign.md)
