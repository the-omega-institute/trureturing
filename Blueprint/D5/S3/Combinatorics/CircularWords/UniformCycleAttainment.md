# Actual Circular Deletion Ambiguity and Attainment

## Abstract

Fix a finite support A in an arbitrary type with decidable equality. States are all nodup oriented Cycle rotation classes with exactly support A; reflection is distinct. For at least four labels, actual labelled deletions of the same original give a history-only correct strategy with mean 2+2/(A.card-1).

Fix a finite support A in an arbitrary type with decidable equality. States are all nodup oriented Cycle rotation classes with exactly support A; reflection is distinct. For at least four labels, actual labelled deletions of the same original give a history-only correct strategy with mean 2+2/(A.card-1).

**Theorem 1.1 (Exactly the Two Cut-Adjacent Slots Collide).**

$$(\mathrm{secondGap}\left(j\right) = \mathrm{secondGap}\left(k\right)) \Leftrightarrow ((j = k) \lor (((j = 0) \land (k = 1)) \lor ((j = 1) \land (k = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/UniformCycleAttainment.rooted_gap_second_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Root a legal first residual at the surviving second label z, writing it z::L, with L nonempty and x fresh. Filtering z from (z::L).rotate j gives L.rotate(j-1), including j=0. Thus the actual second deletion of gapCircle(z::L,x,j) is Cycle(x::L.rotate(j-1)). Anchored injectivity and nodup rotation uniqueness show equality exactly when j=k, or j=0,k=1, or j=1,k=0. The cyclic cut is included; rooting is only a proof aid.

**Theorem 1.2 (One Double Fibre and Otherwise Singletons).**

$$\mathrm{NatCard}\left(\mathrm{doublePairLift}\left(A, x, z\right)\right) = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/UniformCycleAttainment.pair_branch_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For supported distinct x,z and any legal first residual B, restrict SingleDeletionFiberCount.insertionEquiv to second-output index fibres. Its codomain PairLift is the actual subtype of nodup originals with full support A and the two specified deletion outputs. The cut-adjacent index fibre has exactly two members, and every other realized second output has exactly one. R1 also bounds every actual pair fibre by two, including unrealized outputs.

**Theorem 1.3 (Count All Originals Needing a Third Query).**

$$\mathrm{card}\left(\mathrm{ambiguous}\left(A, x, z\right)\right) = \mathrm{mul}\left(2, \mathrm{factorial}\left(\mathrm{sub}\left(\mathrm{card}\left(A\right), 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/UniformCycleAttainment.ambiguous_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is CircularOrderCount.circles A, exactly all legal original cycles, with cardinal (A.card-1)!. Every legal first residual is realized by actual insertion. The candidateSet for a two-entry history is equivalent to PairLift. In each legal first residual exactly two originals lie in its unique double second-output fibre. Partitioning the complete carrier by first residual, whose carrier has (A.card-2)! members, gives ambiguous.card=2*(A.card-2)!. No desired count certificate is assumed.

**Theorem 1.4 (A Decoder Depending Only on History).**

$$\mathrm{decode}\left(\mathrm{run}\left(C\right)\right) = C$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/UniformCycleAttainment.attainingProtocol_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Query fixed supported x,z, and stop if the actual two-observation candidateSet is a singleton. Otherwise query a fixed third supported y and stop. Require x,z,y pairwise distinct. The decoder chooses from candidates determined only by the known support and received history. ThreeSpecifiedDeletions.reconstruct_three makes the three-observation candidate set a singleton. The explicit attainingPolicy reads only the full history and its execute theorem returns exactly the same trace and that trace as terminal label with fuel four. All query outputs are deletions of the same original; neither its hidden state nor a chosen root is available to the protocol.

**Theorem 1.5 (The Actual Strategy Attains the Factorial Ratio).**

$$\mathrm{uniformMeanCost}\left(A\right) = 2 + \frac{2}{\mathrm{sub}\left(\mathrm{card}\left(A\right), 1\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/UniformCycleAttainment.actual_cycle_attaining_mean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual run length is two outside ambiguous and three inside it, so its total cost is 2*(A.card-1)!+2*(A.card-2)!. Prove the factorial recurrence (n-1)!=(n-1)*(n-2)! and positivity before rational division, distinguishing natural subtraction from subtraction in the rationals. The resulting mean is exactly 2+2/(A.card-1). The branch certificate is proved internally from the rooted law, actual insertion equivalence, and full-carrier partition.

For the full optimum, ActualCycleMeanLowerBound identifies the generic first fibre with FirstLift. With a distinct second query the generic paired set is exactly ambiguous intersected with that first fibre, and has two members; a repeated second query leaves all A.card-1 members paired. Hence TwoQueryAmbiguityCost applies to every supported adaptive full-history pointwise-terminating zero-error policy. Together with this actual correct strategy it gives the exact uniform optimum. The final binding-only conjunction is checked transiently. These observation counts do not measure readout bits, object-access cost, time, noisy recovery, or randomized protocols.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/UniformCycleAttainment.actual_cycle_attaining_mean`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/UniformCycleAttainment.ambiguous_card`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/UniformCycleAttainment.attainingProtocol_correct`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/UniformCycleAttainment.pair_branch_exact`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/UniformCycleAttainment.rooted_gap_second_law`
- Dependency: [D5/S3/Combinatorics/CircularWords/CircularOrderCount](CircularOrderCount.md)
- Dependency: [D5/S3/Combinatorics/CircularWords/DeletionReadoutReconstruction](DeletionReadoutReconstruction.md)
- Dependency: [D5/S3/Combinatorics/CircularWords/PairedDeletionFiber](PairedDeletionFiber.md)
- Dependency: [D5/S3/Combinatorics/CircularWords/SingleDeletionFiberCount](SingleDeletionFiberCount.md)
- Dependency: [D5/S3/Combinatorics/CircularWords/ThreeSpecifiedDeletions](ThreeSpecifiedDeletions.md)
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound](../../ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound.md)
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassivePolicyNormalization](../../ConceptDynamics/Experiment/PassivePolicyNormalization.md)
