# Actual Recursive Parent Cycles and Their Chosen Children

## Abstract

Actual Recursive Parent Cycles and Their Chosen Children.

**Theorem 1.1 (Keep Every Supplied Ordinary Cycle Attached).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep.recursive_cycle_from_specified_children_with_inventory`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep.recursive_cycle_from_specified_children_with_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Hamilton path on the special child and a specified Hamilton cycle on each ordinary child, including membership of its literal supplier cut, construct a full parent Hamilton cycle. Every ordinary opening has exactly the edge complement of its particular supplied child cycle, and the chosen pieces retain the exact parent support and edge identities.

**Theorem 1.2 (Choose Actual Ordinary Cycles Once).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep.recursive_cycle_from_special_with_inventory`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep.recursive_cycle_from_special_with_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A supplied special Hamilton path and existence of ordinary child cycles with their actual supplier cuts construct a full parent Hamilton cycle. The output records each chosen child cycle and the exact complement inventory of its opening, so later joint partitions remain attached to the cycles used by the construction.

**Theorem 1.3 (Construct a Parent from an Actual Even State).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep.native_recursive_even_cycle_step`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep.native_recursive_even_cycle_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k=2s+2, the supplied special Hamilton cycle, complete actual partition at special cuts and even boundary endpoints construct the special path. Together with genuine ordinary child cycles and their actual supplier-cut membership, these paths earn a full parent Hamilton cycle. Existence of the prior child cycles and their boundary state remains a hypothesis.

**Theorem 1.4 (Construct a Parent from an Actual Odd State).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep.native_recursive_odd_cycle_step`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep.native_recursive_odd_cycle_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k=2s+3, the supplied special Hamilton cycle, complete actual partition at special cuts and odd boundary endpoints construct the special path. Together with genuine ordinary child cycles and their actual supplier-cut membership, these paths earn a full parent Hamilton cycle. This is a verified recursive constructor, not an unconditional all-size existence assertion.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep.native_recursive_even_cycle_step`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep.native_recursive_odd_cycle_step`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep.recursive_cycle_from_special_with_inventory`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep.recursive_cycle_from_specified_children_with_inventory`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeOuterChildAssembly](NativeOuterChildAssembly.md)
