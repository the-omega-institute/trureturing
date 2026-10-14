# Scheduled realization on original Fibonacci sources and tapes

## Abstract

Restricted finite tables execute actual original requests and hand off original marked tapes.

**Definition 1.1 (Paid chronological request log).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.acquired`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.acquired` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite preselected address list and static source reply, acquired records each actual address and its answer. Preselected mode records the entire list, including repeated addresses and reversed pairs. Stopped mode records the first queried false answer and stops there. It does not seek the actual first absence.

**Definition 1.2 (Readout from the acquired cell).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.cellLabel`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.cellLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The label is chosen from a finite word whose stopped or complete view equals the recorded replies. When the output function is constant on the selected schedule cells, every such word gives the same label. The choice uses only the preselected table and acquired replies; an inconsistent record receives the base label.

**Definition 1.3 (Constructed configurations).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.Config`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.Config` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A configuration stores the remaining schedule, the chronological acquired record, and an optional final label. The reachable record is bounded by the selected finite schedule; the configuration type itself contains arbitrary lists. It imposes no restriction on configuration types of original competing procedures.

**Definition 1.4 (Source-free scheduled instructions).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.program`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.program` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The program receives the stop mode, schedule and whole output table before replies. It requests the next address, stores the answer, and discards the remaining suffix after a queried false answer in stopped mode. Exhaustion makes one silent update selecting the cell label, followed by halt. The source enters only through the reply supplied by the interpreter.

**Definition 1.5 (Full original tape carrier).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.Tape`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.Tape` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Tape is the sum of two copies of positive-integer indices times the real open unit interval. The left tag represents every B block and the right tag every P block. This is the entire original carrier, including its uncountable interval coordinates.

**Definition 1.6 (Actual original marks).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.mark`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.mark` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mark j is the point with left tag, block index one, and interval coordinate one divided by j plus two. Every mark lies in B_1.

**Definition 1.7 (Unchanged original consumer).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.consumer`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.consumer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The consumer returns unknown on every left-tagged B block and proposes the positive block index on every right-tagged P block. A selected mark is a handed tape; it is never interpreted as a proposal of its mark index.

**Definition 1.8 (Actual original Fibonacci sources).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.Source`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.Source` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A source is a pair r,g with prime r and integer g between the ceiling of F_r/10 and the floor of F_r/5. All labels are retained; no probability law on sources is introduced.

**Definition 1.9 (Actual prime replies).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.reply`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.reply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Natural address i denotes the original prime index i+1, using the increasing enumeration Nat.nth Nat.Prime. The reply tests divisibility of the static integer 1+F_r*g by that prime.

**Definition 1.10 (Same-source marked-tape handoff).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.handoff`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.handoff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Handoff keeps the actual source coordinate and declares the original mark stored in the final configuration. The original consumer is then applied to that tape on the same source. The preparation record is not a second consumer input.

**Theorem 1.11 (Every restricted table executes on every actual source).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.original_scheduled_realization`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.original_scheduled_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every active length L, including zero, and either stop mode, choose once a representing schedule for every complete catalog table. Every schedule has at most two entries, all below L, and is strictly increasing in stopped mode. For every table and every actual Fibonacci source, the common program has a finite StateTransition evaluation from its source-independent initial configuration. Its terminal configuration contains exactly that source's acquired schedule log and the table label at the entire actual low word. The paid log has length at most two and its reply sequence is exactly the scheduled view.

The proof constructs the actual finite path by induction on the remaining schedule. Each read appends exactly one address-answer pair to both stored record and interpreter log. After a stopped false answer the remainder is empty. Exhaustion makes a silent cell-label update; the final configuration then halts. The existing queried-view congruence of OriginalScheduledWitnessTables identifies the actual reply cell with the finite low word. Cell invariance, rather than an assumed execution-to-table transport field, identifies the label.

The same terminal configuration hands the actual mark to the unchanged consumer, with the source coordinate retained. That consumer returns unknown because all marks lie in B_1. The result includes empty schedules (also representing the low restriction of original high-only schedules), preselected repetitions and reversal, stopped cells 0/10/11, arbitrary later-zero patterns, and L=0. It does not assert that a queried zero is the actual first absence or that a label was queried.

For one probability vector w on complete tables, enumerate the finite catalog by Fin N. Let C_i be the sum of the first i real masses, so C_0=0 and C_N=1, and assign table i the interval Ico(C_i,C_(i+1)). Use the single seed U in Ico(0,1), with the pullback of Lebesgue measure under the subtype inclusion. This is a probability measure. Consecutive interval coverage and monotone disjointness select exactly one whole table at each U; equal boundaries give empty intervals, so zero weights need no special selection. The selected table is measurable because every fiber is the corresponding interval. Real.volume_Ico gives its exact mass w_i, and finite singleton extensionality gives the entire common PMF law. The program and initialization depend on this table and its fixed representative schedule before any source reply. At each fixed actual source, finite record and handed-tape events are measurable pullbacks from that same finite table space. The tape law is exactly the pushforward of w by its table label and the actual mark embedding. For two allocations with boundaries C and D on the same U, the joint cell i,j is Ico(max(C_i,D_j),min(C_(i+1),D_(j+1))). Set.Ico_inter_Ico gives this common refinement, and each marginal retains its own PMF. The common refinement selects both allocations from the same seed without asserting their independence. No terminal randomness is added.

For a finite mark law p and an actual first absence n>L, the full-carrier event-supremum TV equals max(1-p(0),a_n). To bound every measurable event, split according to whether it contains theta_0 and theta_n. An event excluding theta_0 has p mass at most 1-p(0), and its target mass at most a_n. An event containing theta_0 has p mass at least p(0); if it also contains theta_n its target mass is one, and otherwise its target mass is 1-a_n. These four cases give the upper bound. The finite set of positive retained marks and the singleton theta_n give the two lower bounds. Singleton measurability and finite measure identities apply on the entire original carrier. Thus no restriction of the event supremum or half-TV normalization is used. This application is a binding of existing event and finite-mass supplies; it adds no retained theorem.

Use zero-based a(i)=a_(i+1). Vanishing of a and epsilon>0 give a first index L with a(L)<=epsilon. Antitonicity proves i<L exactly when a(i)>epsilon, and a(i)<=epsilon for every i>=L. The actual low-word first false index is min(firstIndex(x),L). If firstIndex(x)<L, mapping eta_b through the mark embedding gives the exact original selected law, so measurable TV contraction supplies the actual cap. Otherwise the low word is all positive, its finite cap gives 1-p(0)<=epsilon, and the exact tail maximum together with a_n<=epsilon gives the same original cap. Equality a_n=epsilon is included. At epsilon=1 the original a(0)<=1 forces L=0, and every representing schedule is empty. Combining this cap application with the interval sampler and the constructed execution gives one source-independent uniform-seed acquisition with measurable records, finite handoff for every seed, at most two paid requests, and the unchanged consumer on the same actual source. The required inequalities hold for the mixed law, rather than each individual selected table.

The retained theorem supplies the constructive execution leg, and these exact applications supply closed-cap realization for a feasible distribution on either restricted catalog. Identifying the stopped catalog laws with the original coefficient criterion C_L requires the still separate original iff O_L=C_L of Section 109.1. The complete original Theorem 110.2 is not asserted here.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.Config`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.Source`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.Tape`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.acquired`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.cellLabel`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.consumer`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.handoff`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.mark`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.original_scheduled_realization`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.program`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization.reply`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables](OriginalScheduledWitnessTables.md)
