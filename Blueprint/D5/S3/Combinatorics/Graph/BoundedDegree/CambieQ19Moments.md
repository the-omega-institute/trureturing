# Transporting counts and orders from the actual graph

## Abstract

The two graph equivalences transport the four moments to sums over the same support configurations with different weights.

**Definition 1.1 (Actual nonempty tree subgraphs).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.Subtrees`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.Subtrees` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each element is a host subgraph whose graph on its vertex type is a tree.

**Definition 1.2 (Classifying the full tree type).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.allTreesEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.allTreesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An actual tree of the witness gives its support configuration together with the associated deletion choice.

**Definition 1.3 (Finiteness of the support configurations).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.instFintypeConfiguration`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.instFintypeConfiguration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite enumeration of actual connected supports transports across the support equivalence.

**Definition 1.4 (Finiteness of each deletion fiber).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.instFintypeDeletionChoices`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.instFintypeDeletionChoices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each choice type is finite since the host cycles have finitely many edges.

**Theorem 1.5 (The connected-set count).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.connectedCount_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.connectedCount_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The connected-support count equals the number of configurations.

**Theorem 1.6 (The connected-set order sum).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.connectedOrder_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.connectedOrder_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The total connected-set order equals the sum of the decoded order over configurations.

**Theorem 1.7 (The subtree count).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.subtreeCount_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.subtreeCount_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original order-stratified count equals the sum over configurations of their deletion-choice multiplicities.

**Theorem 1.8 (The subtree order sum).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.subtreeOrder_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.subtreeOrder_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original order-stratified total order equals the sum of each decoded order multiplied by its deletion-choice multiplicity.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.Subtrees`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.allTreesEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.connectedCount_transport`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.connectedOrder_transport`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.instFintypeConfiguration`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.instFintypeDeletionChoices`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.subtreeCount_transport`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.subtreeOrder_transport`
- Dependency: [D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices](CambieQ19TreeChoices.md)
