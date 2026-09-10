# Finite Graph Reconstruction

## Abstract

Structural finite graphs reconstruct functions on exactly their archived domain.

**Definition 1.1 (Exact functions and legal HF graphs).**

Lean statement: `D5/S0/History/Spacetime/FiniteGraphEncoding.graph_code_equiv`

*Formalization.* `D5/S0/History/Spacetime/FiniteGraphEncoding.graph_code_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The independent graph predicate requires totality and a unique legal value at each archived input, and excludes every other entry. Decoding chooses that unique value only on the finite domain. The representation uses the proved equivalence for its value carrier.

**Theorem 1.2 (Reconstruction loses no graph entries).**

Lean statement: `D5/S0/History/Spacetime/FiniteGraphEncoding.encode_decodeGraph`

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/FiniteGraphEncoding.encode_decodeGraph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unique lookup recovers every member of a legal graph. Extensional HF equality proves the reverse round trip. The module also represents arbitrary relations with archived endpoints and arbitrary subsets of the archive, each with both round trips.

## References

- Truth anchor: `D5/S0/History/Spacetime/FiniteGraphEncoding.encode_decodeGraph`
- Truth anchor: `D5/S0/History/Spacetime/FiniteGraphEncoding.graph_code_equiv`
- Dependency: [D5/S0/History/Spacetime/HFEncoding](HFEncoding.md)
