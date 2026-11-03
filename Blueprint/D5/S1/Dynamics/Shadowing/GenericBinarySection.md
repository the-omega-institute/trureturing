# Generic binary names and a convergent section

## Abstract

Complete binary graph languages admit a locally deciding name and a compact first-disagreement section.

**Theorem 1.1 (Locally deciding binary name).**

Lean statement: `D5/S1/Dynamics/Shadowing/GenericBinarySection.exists_binary_name_locally_deciding`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/GenericBinarySection.exists_binary_name_locally_deciding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

For every countable family of closed subsets of the binary name space, there is a binary name a such that each family member has an open neighborhood of a contained in it or in its complement. The countability is over the closed family itself.

**Theorem 1.2 (Complete finite graph languages are closed).**

Lean statement: `D5/S1/Dynamics/Shadowing/GenericBinarySection.initialGraphLanguage_isClosed`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/GenericBinarySection.initialGraphLanguage_isClosed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

A finite directed graph with binary edge data, a continuous finite-alphabet label, and an arbitrary initial vertex set determines a closed set of complete infinite names. The compact space of all complete paths, including the initial restriction, maps continuously to its label image.

**Theorem 1.3 (One name decides every finite graph code locally).**

Lean statement: `D5/S1/Dynamics/Shadowing/GenericBinarySection.exists_generic_finite_graph_decision`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/GenericBinarySection.exists_generic_finite_graph_decision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

Boolean edge, label, and initial-vertex data give a countable family of all finite binary graph languages. A Baire-generic binary name locally decides every language in this family. No restriction on the clopen subsets of another space is imposed.

**Theorem 1.4 (Continuous first-disagreement map).**

Lean statement: `D5/S1/Dynamics/Shadowing/GenericBinarySection.continuous_firstDifference`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/GenericBinarySection.continuous_firstDifference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

The map from binary names to the one-point compactification of the naturals sends a name to its first disagreement with a fixed name a, and sends a itself to infinity. Finite disagreement fibres are clopen, and agreement on any finite prefix gives continuity at a.

**Theorem 1.5 (A compact convergent section).**

Lean statement: `D5/S1/Dynamics/Shadowing/GenericBinarySection.exists_firstDifference_section_homeomorph`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/GenericBinarySection.exists_firstDifference_section_homeomorph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

The set consisting of a and the names obtained by flipping exactly its nth bit is compact. Restricting firstDifference to this set gives a homeomorphism onto the one-point compactification of the naturals.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/GenericBinarySection.continuous_firstDifference`
- Truth anchor: `D5/S1/Dynamics/Shadowing/GenericBinarySection.exists_binary_name_locally_deciding`
- Truth anchor: `D5/S1/Dynamics/Shadowing/GenericBinarySection.exists_firstDifference_section_homeomorph`
- Truth anchor: `D5/S1/Dynamics/Shadowing/GenericBinarySection.exists_generic_finite_graph_decision`
- Truth anchor: `D5/S1/Dynamics/Shadowing/GenericBinarySection.initialGraphLanguage_isClosed`
