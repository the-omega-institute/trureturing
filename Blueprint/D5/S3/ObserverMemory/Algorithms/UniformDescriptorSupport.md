# Effective presentations and exact native halt support

## Abstract

Effective original presentations and exact same-source native halt support.

The full register carrier S contains a subtype D of original sources. Update acts on S and need not preserve D. Read observes U iterated j times on the original source. A chart constructor accepts only admitted coordinates; the disjoint chart union is bijective with D, including empty families and zero-dimensional charts. Complete target rows and their supplied default are retained as actual data.

**Definition 1.1 (The original task).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.Task`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.Task` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The permitted physical domain consists of finite words over a supplied finite alphabet, with effective membership. Replies have a fixed nonempty finite order. The supplied target returns the entire row of an original source; it is never computed from an arbitrary transported register.

**Definition 1.2 (Exact supplied maps and predicates).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.Presentation`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.Presentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Admission, whole-row Same, descriptor validity and all-source all-epoch Reply are actual Presburger syntax. Theta, literal choice, literal coverage and complete-row construction are supplied implementation data. Semantic assumptions are proof fields. Coverage says membership in Real, and permits a noncanonical physical realization. Descriptor choice has no source, chart or epoch argument.

**Definition 1.3 (Reached content, absence and rank).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.ReachedTransport`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.ReachedTransport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Content is defined only on reached registers. Persistence, its additive transport action and nondecreasing decoded rank retain the reached-address interpretation. The absent symbol, when present, has rank zero. The finite rank map strictly preserves the given reply order.

**Theorem 1.4 (Rank monotonicity on one original source).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.rank_monotone`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.rank_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Direct substitution of the supplied decode and transport laws, with the zero-rank minimum in the absent case, gives monotonicity at every permitted literal on the same original source. The transported register is used directly; no source constructor or chart inverse is applied after update.

**Definition 1.5 (Stored instructions).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.InstalledEntry`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.InstalledEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A read stores one permitted literal and a tabulated vector of reply successors. An update stores one successor. A halt stores one complete row. No descriptor, chart selector, source coordinate, phase witness or epoch port is installed.

**Definition 1.6 (A complete materialized installation).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.InstalledTable`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.InstalledTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial state and every entry are present in an eager vector, including unreachable entries. A runtime function which invokes a solver, realizer, Theta or target constructor is not this installation. The data type specifies the storage boundary; arithmetic witness extraction constructs it separately.

**Definition 1.7 (Literal execution with the stored row).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.Successful`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.Successful` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original source, a native finite Run reaches a halt whose stored complete row equals that source target. This condition is stronger than graph Total and Shared alone.

**Definition 1.8 (Graph and descriptor type choices).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.TypedEntry`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.TypedEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each read occurrence has its own finite descriptor type and every reply successor. Update and halt choices remain available when the type alphabet is empty. Parameters are not enumerated or numerically bounded.

**Definition 1.9 (Every finite control label is retained).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.reindexSkeleton`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.reindexSkeleton` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A supplied equivalence sigma maps the original initial state and each successor. At numeric state i the complete entry is read at sigma inverse i. Every state is retained, including unreachable states. Type assignment is required only at original reads, so no artificial type inhabitant is needed for read-free tables.

**Definition 1.10 (All entry alternatives).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.entryList`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.entryList` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Explicit finite products enumerate every type and every reply-successor vector, every update successor, and halt. Successors are eagerly tabulated vectors.

**Definition 1.11 (All complete labeled skeletons).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.skeletonList`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.skeletonList` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An explicit product enumerates each initial state and every state entry. No reachability pruning or numerical descriptor cutoff occurs.

**Theorem 1.12 (Enumeration has no missing skeleton).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.skeletonList_complete`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.skeletonList_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every complete typed skeleton belongs to the executable list by List.mem_pi, List.mem_map and List.mem_flatMap. These consumed product bindings preserve all entries. The retained symbolicTable construction uses reindexSkeleton; native state and address transport supplies its operational correspondence.

**Definition 1.13 (All sizes one through K).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.candidates`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.candidates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The list contains every skeleton of each positive size at most K. Budget zero gives the empty list. Empty descriptor types leave update and halt graphs intact.

**Definition 1.14 (Fixed numeric descriptor blocks).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.blockIndex`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.blockIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read occurrence a has offset equal to the sum of all earlier descriptor dimensions. Its local parameter k has numeric index offset plus k. The total is the sum of all block widths; a zero-width block contributes no coordinate.

**Theorem 1.15 (Different blocks do not overlap).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.blockIndex_injective`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.blockIndex_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pinned finSigmaFinEquiv and finSigmaFinEquiv_apply identify this offset map with the standard finite sigma equivalence; List.sum_take_ofFn supplies the prefix-sum correspondence. This consumed binding gives disjoint numeric intervals for distinct read occurrences. Two occurrences may install the same physical literal while keeping distinct descriptor blocks. Every visit and every phase formula uses the same blockIndex map.

This syntax is the arithmetic component of the whole literal-table synthesis. It consumes the native fixed-response path and final-unit-update crossing formulas and the native phase partition theorem. Supplied presentation maps interpret only admitted source tuples. The formulas contain one common descriptor tuple and one source tuple shared by every phase.

**Definition 1.16 (Capture-avoiding block quantification).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.closeEx`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.closeEx` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing Presburger bounded-formula relabel and exs APIs bind an explicitly sized numeric block. closeAll uses the corresponding universal API. Empty quantifier blocks retain their logical meaning.

**Definition 1.17 (Finite conjunction and disjunction).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.allF`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.allF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The list folds use true for empty conjunction and false for empty disjunction. anyF forms the disjunction. These are actual existing Presburger syntax, not an additional arithmetic language.

**Definition 1.18 (Exact shared-source epoch guards).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.gamma`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.gamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every guarded epoch reads the same free source tuple and the same descriptor block for each occurrence. Source variables, descriptor variables, guard endpoints and the bound epoch have disjoint tagged embeddings. For D descriptor coordinates and d source coordinates, the standard finSumFinEquiv flattening sends descriptor k to k and source i to D+i. In a phase body the terminal epoch has index D+d, phase endpoint t_i has index D+d+1+i, and phase count d_i has index D+d+1+(l+2)+i. The guard-bound epoch is a fresh inner quantifier. Constructor separation and the capture-avoiding relabel realization equations prove these blocks do not alias. The independent Shared source m has index D+d+m in its two-source scope; each H binds its own fresh terminal epoch and phase block.

**Definition 1.19 (A native phase chain in finite syntax).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.phaseDisjunct`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.phaseDisjunct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All phase endpoints and update counts are independently bound. Internal crossings finish in a genuine unit update. The last path ends at J, while J plus one is only the right delimiter of its guard. Graph coefficients in path progressions are computed numerals; no two unbounded variables are multiplied.

**Definition 1.20 (A finite complete phase enumeration).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.haltEpochFormula`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.haltEpochFormula` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The list ranges over every permitted phase count, every response vector at each phase and every intermediate control. The maximum rank times the number of actual reads bounds phase count only, with no bound on phase duration, runtime, epochs or literal length.

**Definition 1.21 (Dimensions for actual read occurrences).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.dims`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.dims` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit finite subtype enumeration lists exactly read controls. Each selected type supplies its own numeric dimension, including zero. No artificial observation port is added to the installed control state.

**Definition 1.22 (One assignment reused at every visit).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.descriptorTuple`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.descriptorTuple` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every local coordinate is read through the fixed blockIndex of its occurrence. The resulting descriptor is shared across all charts, epochs and phase visits.

**Definition 1.23 (All permitted realizations).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.Realizes`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.Realizes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A literal assignment requires Real membership for each descriptor. It permits duplicates and noncanonical choices. It requires no equality to chosenLiterals.

**Definition 1.24 (Original-source halt at an unbounded epoch).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.haltAt`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.haltAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native phase formula is instantiated with the original source chart, its admission and exact descriptor replies. Its eventual projection H independently quantifies that source terminal epoch.

**Theorem 1.25 (Exact native literal execution).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.native_support`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.native_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On admitted coordinates and a valid common tuple, haltAt is equivalent to native Run at J, and H is equivalent to existence of a native Run at some J. The theorem accepts every Real-compatible literal assignment. Arbitrary noninjective address transport identifies occurrence observations with the physical literal program. A halt endpoint gives the native first-arrival interpretation; the theorem also keeps general finite endpoints exact. It certifies no stored output row.

**Definition 1.26 (Proof interpretation of the literal graph).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.literalProgram`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.literalProgram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This map interprets the graph through the native arbitrary-address transport API. It supplies native execution semantics for proofs. It is not asserted to be a stored table, and does not construct any halt row.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.InstalledEntry`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.InstalledTable`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.Presentation`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.ReachedTransport`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.Realizes`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.Successful`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.Task`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.TypedEntry`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.allF`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.blockIndex`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.blockIndex_injective`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.candidates`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.closeEx`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.descriptorTuple`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.dims`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.entryList`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.gamma`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.haltAt`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.haltEpochFormula`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.literalProgram`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.native_support`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.phaseDisjunct`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.rank_monotone`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.reindexSkeleton`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.skeletonList`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport.skeletonList_complete`
- Dependency: [D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger](FixedResponsePresburger.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport](NativeExecutionTransport.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/ResponsePhasePartition](ResponsePhasePartition.md)
