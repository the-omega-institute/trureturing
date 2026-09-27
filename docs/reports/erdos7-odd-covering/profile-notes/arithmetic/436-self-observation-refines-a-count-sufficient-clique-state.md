[Index](../../marked_head_profile.md) · [Original-label clique DP](433-chordal-overlap-certificates-and-their-exact-finite-limits.md)

# A count-sufficient E7 state need not answer its own archive

For one fixed original congruence family, the clique DP state `(A,d)` suffices for its residual-mass evaluation. It need not identify the original CRT cell or an actually executed branch record. Adding an authorized read of that record can strictly refine the required state without changing the original covering truth. The repair is relative to the declared future operations: a current CRT residue repairs cell identification, while arbitrary archive queries require more information.

## 1. The old task and a literal same-input counterexample

Fix the original family once:

    S = (0 mod 3, 0 mod 5, 1 mod 15),

and use elimination order 3,5,15. Its compatibility graph has just the edge 3--5. The original survivor density is exactly 7/15: the zero classes modulo 3 and 5 cover seven residues modulo 15, and the class 1 modulo 15 adds one more.

The evaluator's value is

    P(A,d) = sum_{T clique in G[A]} (-1)^|T| / lcm(d,m_T).

The fixed moduli and compatibility graph remain inputs to the evaluator. `(A,d)` is its memoization key within those inputs; it is not claimed to encode an arbitrary unknown family.

Two actually executed recursion histories are:

| history | executed decisions | selected original labels | final `(A,d)` | current CRT cell | `P(A,d)` |
|---|---|---|---|---|---|
| h0 | include 3; include 5 | {3,5} | (empty,15) | 0 mod 15 | 1/15 |
| h1 | skip 3; skip 5; include 15 | {15} | (empty,15) | 1 mod 15 | 1/15 |

In h0, the incompatible 15-label is removed by the actual neighbor restriction; no fictitious “skip 15” observation is inserted. Every phase is the same fixed phase from S in both histories. An include/skip decision selects a term in the exact recurrence; it never selects a new congruence phase.

The old task returns the same mass, so merging these calls is correct. If the observer retained its actual decisions and has permission to read them, the new operation

    SelfRead(first executed decision was include)

returns true on h0 and false on h1. Thus this task cannot factor through `(A,d)`. The selected intersection's original residue also cannot factor through `(A,d)`, since it is 0 on h0 and 1 on h1. These are failures of the enlarged task interface, not errors in the original count.

The signed contribution of a recursion call is another distinct task: the outer recurrence supplies its sign/context. `P(A,d)` alone is the nonnegative reachable-state mass, not that entire caller context.

## 2. What must be added

For the one displayed self-read, the pair `(A,d,firstDecisionBit)` is the least augmentation retaining the old key and answering that bit. More generally, a readout q answers a new target t exactly when t is constant on every q-fiber. Adjoining t gives

    ker(q,t) = ker(q) intersect ker(t),

with strict inclusion exactly when two q-equal histories have different t-values. A redundant target does not refine the kernel. No deterministic postprocessing of the old key can recover the separating bit.

For current cell identification, retain its original CRT residue r modulo d:

    (A,d,r),  intersection(selected original classes) = r mod d.

On an include step, r is updated by the generalized CRT using the newly included label's fixed original phase; on a skip step it is retained. This restores current-cell queries in a fixed reference frame. It does not, in general, restore all history queries.

A separate fixed-family control makes that limitation explicit. Keep all phases fixed at zero in `(0 mod 3,0 mod 5,0 mod 15)`. The histories

    include 3; include 5; skip 15,
    skip 3; skip 5; include 15

both end at `(A,d,r)=(empty,15,0)`, while their first executed decision bits differ. The two phases assignments in this section are separate control inputs; neither control changes a phase between branches.

A full original-phase archive by itself still does not reconstruct the branch choices: all branches of either fixed input already share that archive. A sufficient raw implementation for all declared provenance tasks retains the original input and label identities, the actual executed include/skip record, the reference-frame map, and any control or permission state that affects allowed replies or updates. A smaller implementation may quotient this data by equality under the declared future protocols.

For dynamics, one-step query sufficiency is not the whole requirement. The state must also preserve action legality, replies, and successor equivalence. The canonical repair records the old readout and the requested outputs after every allowed finite action word, then quotients by equality of that behavior. If permissions vary by state, denied operations must be represented consistently, for example by an explicit denial reply and a fixed denial transition. This is a modeling obligation, not permission supplied by the mathematical quotient.

## 3. A canonical state is not automatically accessible information

The full mathematical configuration can contain a source archive, reference, and control state without exposing them to the observer. An observer action must be chosen from what its actual readable record distinguishes. Merely defining `(A,d,r,archive)` does not establish that the observer has obtained r or can read archive.

The self-read counterexample assumes that the branch decisions were actually retained and that the new operation is permitted to read the selected bit. If only `(A,d)` was retained and the decisions were erased, adding the name `SelfRead` cannot reconstruct them. The system must retain the needed data from the start or acquire it through a justified additional observation. A requirement for different actions on two identical readable records is not implementable by a policy of that record alone.

For a fixed deterministic update/readout system, the complete behavior quotient has well-defined transitions. Finiteness must apply to the whole joint state, including the retained memory and control. A finite arithmetic carrier with an unbounded archive is not automatically a finite joint-state system.

For a fixed finite system and fixed operation language, refinement eventually stabilizes. Enlarging the operation language changes that fixed problem: an old stable quotient can split again. Even on a finite carrier, one observed plateau in an arbitrary sequence of newly introduced tasks does not imply permanent stability, although there can be only finitely many strict partition refinements. These facts do not imply Gödel incompleteness.

## 4. Reference transport preserves truth, not every untranslated question

A common translation by c sends

    x -> x+c,   a_i -> a_i+c mod m_i

for every original label at once. It preserves each incidence statement and hence coverage and survivor mass:

    x = a_i mod m_i iff x+c = a_i+c mod m_i.

For example, the all-zero phases at moduli 3,5,15 and the all-one phases have identical compatibility graphs and survivor density 8/15. Their archive answer “what was the original phase modulo 3?” is different. Moreover the unchanged literal point 0 is covered by the first family and uncovered by the second. This does not violate transport: the transported comparison pairs old 0 with new 1.

A centered representation can answer original-coordinate queries only if its reference map is retained or otherwise available. The existence of a legal common translation does not mean an observer has read its parameter. This construction never uses separately chosen phases in different branches.

## 5. Exact existing Lean interfaces

The following existing declarations supply the general bridge. They are existing results being instantiated or composed; this control introduces no new Lean theorem or wrapper. The paths refer to the main repository tree, whose declaration bodies and frozen-state entries were inspected. No new scoped Lean build was run for this read-only review, and no claim of newly machine-checked E7 specialization is made.

| needed statement | existing declaration and module |
|---|---|
| Enlarging a task/profile family cannot enlarge its equality kernel | `intervention_family_kernel_monotonicity`, `D5/S3/ConceptDynamics/RefinementFactorization/InterventionFamilyKernelMonotonicity.lean`; “intervention” may be instantiated by a declared protocol with its reply law |
| A new read splits the old quotient exactly when it separates an old fiber | `protocol_innovation_iff_separates_current_fiber`, `D5/S3/ConceptDynamics/ExperimentBoundary/ProtocolInnovationCriterion.lean` |
| Adjoining the old readout and all requested target values is the coarsest jointly sufficient readout | `target_family_completion_is_coarsest`, `D5/S3/ConceptDynamics/Completion/TargetFamilyCompletionMinimality.lean` |
| A unique factor on realized images exists exactly when the finer readout's kernel is contained in the coarser one | `refinement_iff_kernel_inclusion_on_effective_images`, `D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion.lean` |
| Action-word completion is the least interface stable under every generating action | `controlled_completion_is_least_stable_refinement`, `D5/S3/ConceptDynamics/ControlledCompletion/LeastStableRefinement.lean` |
| Every controlled update descends uniquely on complete behaviors | `all_interventions_unique_completion_descent`, `D5/S3/ObserverMemory/Dynamics/ControlledInterventionDescentUniqueness.lean`; underlying `dynamics_descends_iff`, `D5/S0/Rewriting/Quotients/DynamicsDescent.lean` |
| Fixed finite controlled refinement stabilizes, and one fixed-operator stable step is permanent | `controlled_finite_stability`, `D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability.lean`; its signature requires finite nonempty state/input/output carriers and a surjective readout onto the realized outputs |
| State-only equality need not imply record-readout equality | `state_record_readout_distinguishability`, `D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability.lean`; it uses a certified actual history evolution and a readout of its record, not an independently supplied fake archive |
| Postprocessing cannot recover a distinction erased by a readout | `postprocessing_kernel_mono`, `D5/S3/ConceptDynamics/Postprocessing/PostprocessingKernelMonotonicity.lean` |
| Identical accessible states cannot support different prescribed actions under a memoryless policy | `no_memoryless_policy`, `D5/S3/ConceptDynamics/Policy/MemorylessActionObstruction.lean` |
| Transported answers require both source/target and readout commuting equations | `effective_image_naturality`, `D5/S3/ConceptDynamics/Transport/EffectiveImageNaturality.lean` |

The common-translation calculation and the two explicit E7 history controls are ordinary arithmetic specializations. They do not require an additional binding declaration. The missing unrestricted E7 positivity theorem is unchanged by this task-interface refinement.

## 6. Reusable finite control

[observer-task control](../../frontier/cover-geometry/observer_task_extension.py) uses only the standard library, keeps each input's original phases fixed, constructs the actual include/skip histories, compares the clique recurrence with literal residue counts, checks the archive and CRT queries, and verifies common translation point by point. Run:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/observer_task_extension.py

The program writes its exact control values to standard output. Explicit failures remain active under `-O`. The original family retains survivor density 7/15 before and after adding the archive task; only the required state partition changes.
