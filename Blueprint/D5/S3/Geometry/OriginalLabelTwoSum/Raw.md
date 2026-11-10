# Raw

## Abstract

Literal downward face families preserve original grounds and the empty-face distinction before native projection.

**Definition 1.1 (Family).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.Family`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.Family` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual source declaration; elaboration, native selection and audits remain OPEN.

**Definition 1.2 (Supported).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.Supported`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.Supported` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Ground support includes every face, including the empty face when present. 

**Definition 1.3 (delta).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.delta`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The raw simplex on the given original labels. In particular delta empty is UNIT. 

**Definition 1.4 (Rows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.Rows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.Rows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Original rows are indexed, even when two rows have identical complements. 

**Definition 1.5 (root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.root`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

No row means VOID; an empty complement of an existing row contributes UNIT. 

**Definition 1.6 (without).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.without`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.without` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Row deletion is restriction of the index type, and does not delete a vertex. 

**Definition 1.7 (restrict).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.restrict`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.restrict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal simplicial deletion on the specified surviving ground. 

**Definition 1.8 (rawLink).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.rawLink`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.rawLink` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Link preserves absence of the raw empty face. 

**Definition 1.9 (rawJoin).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.rawJoin`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.rawJoin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Augmented join on the same original ambient type; support/disjointness is proved by consumers. It does not silently supply an empty factor. 

**Definition 1.10 (project).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.project`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.project` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Projection discards just the empty face, after all raw operations. 

**Definition 1.11 (nativeAug).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.nativeAug`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.nativeAug` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reuse the native owner's augmentation ONLY when a raw-empty witness is available at the call site. It is not an inverse projection on VOID. 

**Theorem 1.12 (project_nativeAug).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.project_nativeAug`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Raw.project_nativeAug` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reuse the native owner's augmentation ONLY when a raw-empty witness is available at the call site. It is not an inverse projection on VOID. 

**Theorem 1.13 (reconstruct_nonvoid).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.reconstruct_nonvoid`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Raw.reconstruct_nonvoid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This reconstruction REQUIRES raw empty membership, rather than identifying VOID with UNIT through their common nonempty projection. 

**Theorem 1.14 (raw_ext).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.raw_ext`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Raw.raw_ext` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native skeleton determines the raw family only once raw empty membership is supplied. This theorem is used for non-VOID filling and Gamma endpoints. 

**Theorem 1.15 (mem_delta).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.mem_delta`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Raw.mem_delta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native skeleton determines the raw family only once raw empty membership is supplied. This theorem is used for non-VOID filling and Gamma endpoints. 

**Theorem 1.16 (mem_project).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.mem_project`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Raw.mem_project` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native skeleton determines the raw family only once raw empty membership is supplied. This theorem is used for non-VOID filling and Gamma endpoints. 

**Definition 1.17 (Root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.Root`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.Root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full original ground is independent of which singleton faces occur. 

**Definition 1.18 (asRoot).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.asRoot`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.asRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full original ground is independent of which singleton faces occur. 

**Definition 1.19 (phi).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.phi`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact parent formula; R is never a fake coordinate e. 

**Theorem 1.20 (root_supported).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.root_supported`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Raw.root_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complement roots are supported even when their row family is empty. 

**Theorem 1.21 (rawJoin_void).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.rawJoin_void`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Raw.rawJoin_void` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complement roots are supported even when their row family is empty. 

**Theorem 1.22 (rawJoin_unit).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.rawJoin_unit`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Raw.rawJoin_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complement roots are supported even when their row family is empty. 

**Theorem 1.23 (join_split).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.join_split`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Raw.join_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split coordinates are unique on disjoint original grounds. 

**Definition 1.24 (substitute).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.substitute`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.substitute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every original row is retained in this literal substitution. This is raw presentation transport, not a claimed graph unique-path substitution theorem. 

**Definition 1.25 (transportedRows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.transportedRows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Raw.transportedRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Indexed complementary rows after replacement, on the actual new ground. 

**Theorem 1.26 (row_transport).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.row_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Raw.row_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal transport membership. The proof keeps the original chord indices; redundant rows and UNIT-producing complements are not discarded. 

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.Family`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.Root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.Rows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.Supported`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.asRoot`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.delta`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.join_split`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.mem_delta`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.mem_project`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.nativeAug`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.phi`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.project`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.project_nativeAug`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.rawJoin`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.rawJoin_unit`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.rawJoin_void`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.rawLink`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.raw_ext`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.reconstruct_nonvoid`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.restrict`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.root_supported`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.row_transport`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.substitute`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.transportedRows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Raw.without`
- Dependency: [D5/S3/Geometry/FiniteRelativeSimplicialCollapse](../FiniteRelativeSimplicialCollapse.md)
