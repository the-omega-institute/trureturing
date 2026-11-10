# Physical interface normalization

## Abstract

Physical interface deletion retains original noninterface indices and is reduced to the existing raw row transport by path-derived interface normalization.

**Definition 1.1 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.kappa).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.kappa`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.kappa` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The physical unordered edge of an original chord index.

**Definition 1.2 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.PhysicalSurvivor).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.PhysicalSurvivor`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.PhysicalSurvivor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Original physical survivor indices, without quotienting any other fiber.

**Definition 1.3 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.physicalRows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.physicalRows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.physicalRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict exactly the index type; ground, labels and rows stay original.

**Definition 1.4 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.E_edge).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.E_edge`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.E_edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unrestricted physical-edge deletion root in the existing raw Family.

**Definition 1.5 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.UniqueInterface).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.UniqueInterface`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.UniqueInterface` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Local U*: uniqueness only over the selected interface, never globally.

**Theorem 1.6 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.rows_eq_of_kappa_eq).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.rows_eq_of_kappa_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.rows_eq_of_kappa_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal physical chords have equal actual path-derived rows, including the reversed orientation. This follows from tree path uniqueness, not an input.

**Definition 1.7 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalizeInterface).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalizeInterface`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalizeInterface` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Normalize only the interface fiber: retain c and every noninterface original index. Every other GraphData field is literally inherited.

**Definition 1.8 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalizedChord).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalizedChord`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalizedChord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The retained distinguished index is c itself, with subtype evidence.

**Theorem 1.9 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalized_row).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_row`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalization changes no row at any retained original index.

**Theorem 1.10 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalized_distinguished_row).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_distinguished_row`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_distinguished_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The interface's actual path row is preserved.

**Theorem 1.11 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalized_root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_root`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete raw root is unchanged, including empty-face membership.

**Theorem 1.12 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalized_uniqueInterface).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_uniqueInterface`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_uniqueInterface` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized presentation has U*, with no restriction on other fibers.

**Theorem 1.13 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.uniqueInterface_iff_survivor_indices).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.uniqueInterface_iff_survivor_indices`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.uniqueInterface_iff_survivor_indices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

U* is exactly the survivor-index identification. No necessity assertion about accidental equalities of raw face sets is made.

**Theorem 1.14 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.E_edge_eq_without).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.E_edge_eq_without`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.E_edge_eq_without` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Explicit local COROLLARY: physical deletion is one-index deletion under U*.

**Definition 1.15 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalizedSurvivorEquiv).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalizedSurvivorEquiv`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalizedSurvivorEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Canonical identity-on-original-indices equivalence after normalized deletion. In particular, duplicate noninterface indices remain distinct.

**Theorem 1.16 (D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalized_without_root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_without_root`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_without_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized one-index deletion is precisely E_edge on the same ground.

**Definition 1.17 (D5.S3.Geometry.OriginalLabelTwoSum.physicalTransportedRows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.physicalTransportedRows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.physicalTransportedRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal corrected row presentation, indexed by old left chords and every original physical right survivor. Its right rows are original actual path rows.

**Theorem 1.18 (D5.S3.Geometry.OriginalLabelTwoSum.normalized_row_transport).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_row_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_row_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both the full right input and the normalized transport output are faithful. The second equality consumes the original row_transport, with the distinguished path row preserved and the deleted-index term replaced by E_edge.

**Theorem 1.19 (D5.S3.Geometry.OriginalLabelTwoSum.physical_row_transport).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.physical_row_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.physical_row_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unrestricted corrected row-algebra parent formula. There is no assumed graph/root equation here. Binding the physical presentation to the actual glued graph requires the independent G1A construction and path theorem.

**Theorem 1.20 (D5.S3.Geometry.OriginalLabelTwoSum.physical_row_transport_of_unique).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.physical_row_transport_of_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.physical_row_transport_of_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Local U* COROLLARY of the unrestricted formula; no global injectivity.

**Definition 1.21 (D5.S3.Geometry.OriginalLabelTwoSum.CyclicInterface.next).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.next`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.next` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Successor around Fin m, written with an explicit wrap for arithmetic proofs.

**Theorem 1.22 (D5.S3.Geometry.OriginalLabelTwoSum.CyclicInterface.cyclic_edge_injective).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.cyclic_edge_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.cyclic_edge_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m>=3, cyclic unordered edges have unique indices. Reversed endpoint matching would force a two-cycle, excluded by m>=3.

**Theorem 1.23 (D5.S3.Geometry.OriginalLabelTwoSum.Wheel.wheel_uniqueInterface).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.wheel_uniqueInterface`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.wheel_uniqueInterface` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual fixed W4 local U*, proved from start/finish via cyclic edges. The general cyclic uniqueness lemma is consumed on the genuine rim endpoints.

**Theorem 1.24 (D5.S3.Geometry.OriginalLabelTwoSum.Wheel.wheel_E_edge).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.wheel_E_edge`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.wheel_E_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Physical W4 deletion is the existing literal E, using the local corollary.

**Theorem 1.25 (D5.S3.Geometry.OriginalLabelTwoSum.Wheel.wheel_physical_row_transport).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.wheel_physical_row_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.wheel_physical_row_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual W4 indexing consumes the corrected raw formula with its existing E. This remains row algebra; no actual glued graph theorem is assumed or claimed.

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.E_edge`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.E_edge_eq_without`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.PhysicalSurvivor`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.UniqueInterface`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.cyclic_edge_injective`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.kappa`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.next`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalizeInterface`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalizedChord`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalizedSurvivorEquiv`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_distinguished_row`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_row`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_row_transport`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_uniqueInterface`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.normalized_without_root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.physicalRows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.physicalTransportedRows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.physical_row_transport`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.physical_row_transport_of_unique`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.rows_eq_of_kappa_eq`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.uniqueInterface_iff_survivor_indices`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.wheel_E_edge`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.wheel_physical_row_transport`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.wheel_uniqueInterface`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Graph](Graph.md)
