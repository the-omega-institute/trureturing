# Sparse original parity and finite recovery

## Abstract

Independent original leaves force a separate actual read in every cone and distinct fixed query controls.

A source is a finite ordered binary tree with alpha and beta leaves. A literal is a Boolean address: false goes left and true goes right. Substitution acts on the same physical tree at every Update. A native controller chooses its next instruction from its control state alone; the source and epoch belong to run semantics and are not extra inputs. Local computation, arbitrary finite address lengths, adaptive Updates and repeated control states are allowed.

**Definition 1.1 (Complete-skeleton address index).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.fullIndex`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.fullIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every address of length depth selects a frontier position of the complete binary skeleton of that depth. This includes the empty address at depth zero.

**Definition 1.2 (Original parity target).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.parity`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.parity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The target is the sum modulo two of h independently chosen Boolean bits. Numerical false denotes an original alpha leaf and true an original beta leaf, so the source Boolean label is the negation of the numerical bit.

**Definition 1.3 (Independent original leaf family).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.source`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.source` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected frontier leaves carry independently varying bits; every unselected frontier leaf is alpha. The selected frontier addresses are required to be distinct in the lower bounds.

**Theorem 1.4 (Every cone is read on the same run).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.parity_read_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.parity_read_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary h and depth, any control type, any fixed native instruction table and initial state, assume every terminating run on every source in the selected family outputs its original parity. Every actual terminating run on each particular source has at least h Read events. For each selected original leaf, that same trace contains a Read at an address extending that leaf address. Soundness is universal over the whole source family, while termination is required only for the run under consideration; h=0 is included.

If one original cone is never read, flip that leaf while keeping all other original labels fixed. Substitution preserves the complete skeleton and all replies outside the flipped cone at every actual epoch. The original chronological trace therefore replays on the flipped source with the same output, contradicting parity soundness. Equal-depth distinct frontier addresses cannot both prefix the address of one Read, so chosen Read occurrences are injectively indexed by the independent leaves.

**Definition 1.5 (Prescribed literal sources).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.originalSource`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.originalSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sourceSlots index places the free leaves at the given ordered list of distinct length-depth literals. All other skeleton leaves retain alpha.

**Theorem 1.6 (Reads, complete controls and Fibonacci capacity).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.literal_parity_lower_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.literal_parity_lower_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h be positive, let q give h distinct literals of one common depth, and let a finite control set C carry a fixed native instruction table and a common initial state. Assume all terminating runs on each originalSource have the correct original parity and every member of the family has a terminating run. Every chosen original literal has its prescribed independent label and every other skeleton leaf is alpha. The controller has at least h+2 states, every terminating run uses at least h Reads, and every injective encoding of C into width-wide Boolean words with no adjacent true bits satisfies h+2 at most Fibonacci(width+2).

The control bound chooses query states from a single actual run. Each state has one fixed materialized address, so the h cones require h different query states. Both parity values occur in the original family; total termination supplies two states with different fixed Halt outputs. Halt and Read states are disjoint. The injection from the sum of these query and Halt indices gives the cardinality bound, and the existing count of admissible words gives the Fibonacci consequence.

**Definition 1.7 (Delayed promised-leaf decoder).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.decodeBit`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.decodeBit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At an even epoch alpha and beta decode as false and true; at an odd epoch beta and branch do. The other two replies are unsupported. The query at index i is q(i) followed by floor(i/2) right edges.

**Definition 1.8 (Finite Q, U and Z table).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.table`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.table` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q vertices have prefixes shorter than h; U vertices have nonempty prefixes shorter than h; Z vertices have bit strings of length h. Q reads the literal selected by prefix length, appends the decoded bit and enters U or the final Z. U updates the same tree and enters Q with the same prefix. Z halts with its fixed vector. Unsupported Read replies hold the current Q vertex. No rejecting vertex is present.

**Theorem 1.9 (Exact original-vector recovery).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.complete_skeleton_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.complete_skeleton_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every depth, ordered address function, nonempty bit vector, common address-length proof and distinctness on the selected indices, the finite table starting at Q of the empty prefix on familySource terminates with that vector. Its chronology has exactly h Reads, h-1 Updates and 2h-1 events. Every supported edge preserves the stated same-source prefix support and lowers rank by one; each Update changes the tree. The initial and final supports hold, only Z rows halt, and unsupported Read replies hold. The root-only h=1 case has no Update.

The recovery theorem uses the existing delayed original-leaf readout and right-spine clock results. The lower bounds concern original parity, whereas this Q/U/Z table returns the entire vector. No exact total vertex count, reachability of every installed vertex, Gray or single-write word implementation, logarithmic width bound, physical tariff, or first-separating-reply certificate is asserted here.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.complete_skeleton_recovery`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.decodeBit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.fullIndex`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.literal_parity_lower_bounds`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.originalSource`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.parity`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.parity_read_lower_bound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.source`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound.table`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](../../../../S1/Words/AdmissibleWords/AdmissibleCount.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout](DelayedOriginalReadout.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativePolynomialDescriptorObstruction](NativePolynomialDescriptorObstruction.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth](NativeSerialDepth.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine](NativeSerialMachine.md)
