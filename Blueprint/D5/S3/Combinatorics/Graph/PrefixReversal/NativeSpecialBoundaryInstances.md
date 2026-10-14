# Even and Odd Native Boundary Assemblies

## Abstract

Even and Odd Native Boundary Assemblies.

**Theorem 1.1 (Consume a Complete Actual Even Boundary).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialBoundaryInstances.native_special_child_even_path`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialBoundaryInstances.native_special_child_even_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k=2s+2, a Hamilton cycle on the native special child with a complete actual special-cut partition and the precise even boundary endpoint relation yields a Hamilton path from right port zero to left port k. The literal route, support counts and retained-edge inventory are constructed from those supplied paths.

**Theorem 1.2 (Consume a Complete Actual Odd Boundary).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialBoundaryInstances.native_special_child_odd_path`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialBoundaryInstances.native_special_child_odd_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k=2s+3, a Hamilton cycle on the native special child with a complete actual special-cut partition and the precise odd boundary endpoint relation yields a Hamilton path from right port zero to left port k. Every output edge belongs to the joined actual paths or a proved native seam; the previous cycle and boundary partition remain inputs.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialBoundaryInstances.native_special_child_even_path`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialBoundaryInstances.native_special_child_odd_path`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialChildAssembly](NativeSpecialChildAssembly.md)
