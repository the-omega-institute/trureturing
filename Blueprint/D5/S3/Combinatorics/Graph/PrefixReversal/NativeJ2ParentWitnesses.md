# Actual Native Two-Label Suppliers and Their Parent

## Abstract

The original raw P and outer Q cycles, their literal joint and restored halves, the actual child openings, and the resulting parent are retained as one construction.

**Theorem 1.1 (Keep the Raw Supplier and All Three Partitions).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall frame \in \mathrm{SupplyFrame}\left(m, 2\right),\; \mathrm{Nonempty}\left(\mathrm{RawSeedFor}\left(m, frame\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses.native_j2_raw_seed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the native F2 witness once. RawSeedFor retains its raw base and closed walk, Hamiltonicity and exact native edge inventory. Its mapped SeedFor retains the same walk through an explicit base equality and heterogeneous walk equality, the six joint pieces and both three-piece halves, their literal ports and simultaneous actual partitions, and all protected-a, remaining-b and selected-c invariants. Both mapped cut groups are explicitly the images of the raw false and true half cuts.

**Theorem 1.2 (Use This Supplier for the Actual Special Path).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall frame \in \mathrm{SupplyFrame}\left(m, 2\right),\; 3 \le \mathrm{Length}\left(\mathrm{Base}\left(frame\right)\right) \Rightarrow \left(\forall seed \in \mathrm{RawSeedFor}\left(m, frame\right),\; \mathrm{Nonempty}\left(\mathrm{SpecialPathFor}\left(frame, seed\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses.native_j2_special_from_raw_seed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a supplied RawSeedFor and base length at least three, map its primary false-half pieces to the equal special domain. Their exact cut image is proved equal to specialCuts and their literal E2 port pairs are earned. The special assembler retains the ordered three pieces, the actual Hamilton path R0 to L2, its full support equality and seam-chain equality, and the uncut edge inventory of this same supplier.

**Theorem 1.3 (Keep the Same Ordinary Supplier Cycle).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall frame \in \mathrm{SupplyFrame}\left(m, 2\right),\; 3 \le \mathrm{Length}\left(\mathrm{Base}\left(frame\right)\right) \Rightarrow \left(\forall gap \in \mathrm{BaseGap}\left(frame\right),\; 1 \le \mathrm{Index}\left(gap\right) \Rightarrow \left(\forall seed \in \mathrm{RawSeedFor}\left(m, \mathrm{nativeChildFrame}\left(frame, gap\right)\right),\; \mathrm{Nonempty}\left(\mathrm{OrdinaryCycleFor}\left(frame, gap, seed\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses.native_j2_ordinary_from_raw_seed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero actual base gap and that child's supplied raw seed, the remaining-b invariant proves membership of the literal supplier cut. OrdinaryCycleFor retains the exact SpecifiedOrdinaryCycle and the base equality and walk-copy equality identifying it with the image of this same seed. Its complete joint and both half partitions therefore remain attached to the cycle that is opened.

**Theorem 1.4 (Keep Every Supplier in Its Actual Parent).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall frame \in \mathrm{SupplyFrame}\left(m, 2\right),\; 3 \le \mathrm{Length}\left(\mathrm{Base}\left(frame\right)\right) \Rightarrow \mathrm{Nonempty}\left(\mathrm{ParentWitnessFor}\left(frame\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses.native_j2_parent_with_raw_witnesses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Construct the special and all base-rotated ordinary suppliers from native F2. ParentWitnessFor retains each raw seed and mapped supplier, the actual special path and every ordinary opening, the exact complement-edge inventory after its own supplier cut, and the resulting full parent Hamilton cycle. It retains the literal child-piece inclusions, the R0 base coordinate, full parent support equality and complete closing seam-chain equality.

**Theorem 1.5 (The Final Child Uses the Original Old P Walk).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall frame \in \mathrm{SupplyFrame}\left(m, 2\right),\; \forall A \in \mathrm{LabelList}\left(m\right),\; \forall u \in \mathrm{Label}\left(m\right),\; \left(\mathrm{Base}\left(frame\right) = \mathrm{Append}\left(A, \mathrm{Singleton}\left(u\right)\right) \land 3 \le \mathrm{Length}\left(A\right)\right) \Rightarrow \left(\forall P \in \mathrm{RawSeedFor}\left(m, frame\right),\; \mathrm{Nonempty}\left(\mathrm{OldPCycleFor}\left(frame, A, u, P\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses.native_j2_old_p_specified_ordinary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For old P with base A appended by u and A of length at least three, the earned native_p_marked_domain_eq_child identity maps the original old P special domain to the final child of its outer frame. This identity preserves every configuration while retaining the old terminal, base and literal port table inside the saved witness. The old P remaining-b invariant proves the actual final supplier cut. OldPCycleFor records the exact same mapped walk through base and walk-copy equalities; no replacement final-child cycle is selected.

**Theorem 1.6 (The Actual Outer Parent Retains Original P and Outer Q).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall frame \in \mathrm{SupplyFrame}\left(m, 2\right),\; \forall A \in \mathrm{LabelList}\left(m\right),\; \forall u \in \mathrm{Label}\left(m\right),\; \left(\mathrm{Base}\left(frame\right) = \mathrm{Append}\left(A, \mathrm{Singleton}\left(u\right)\right) \land 3 \le \mathrm{Length}\left(A\right)\right) \Rightarrow \mathrm{Nonempty}\left(\mathrm{OuterParentWitnessFor}\left(frame, A, u\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses.native_j2_outer_parent_with_raw_p_q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Construct original P and outer Q raw native witnesses and all three actual partitions on each same supplier. Use Q's exact false-half assembly for the special path and P's same mapped cycle for the final child; other children use their retained ordinary suppliers. OuterParentWitnessFor earns an actual Hamilton cycle on the independently defined outer parent and retains the equality attaching its final supplied cycle to the original P witness, every actual opening and complement inventory, literal full support and complete edge chain. Current-parent joint propagation, the next strong StateFor and all-size Hamiltonicity remain subsequent obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses.native_j2_old_p_specified_ordinary`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses.native_j2_ordinary_from_raw_seed`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses.native_j2_outer_parent_with_raw_p_q`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses.native_j2_parent_with_raw_witnesses`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses.native_j2_raw_seed`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses.native_j2_special_from_raw_seed`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2Seed](NativeActualJ2Seed.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentCycle](NativeJ2ParentCycle.md)
