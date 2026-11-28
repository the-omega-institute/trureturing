# Cone attachments through ordinary subdivision

## Abstract

Cone attachments through ordinary subdivision

**Theorem 1.1 (The cone of an adjoined maximum transports two prescribed traces at positive depth).**

Lean statement: `D5/S3/Topology/StableCategory/InheritedDepthConeAttachment.exact_two_cover_of_adjoined_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/InheritedDepthConeAttachment.exact_two_cover_of_adjoined_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

After the first subdivision an adjoined maximum gives a cone attached to the retained region along its strict lower set. At each further subdivision, chains avoiding the apex singleton are added to the retained region and chains with entries containing the apex form the next cone. Erasing the apex lifts to a relative order fence and identifies the new base with the subdivision of the previous base. The retained retraction therefore identifies the base with the actual subdivided interface at every positive depth. A full first trace and an anchor spanning its exclusive complement then yield categorical lower pieces with both old traces after two further ordinary subdivisions.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/InheritedDepthConeAttachment.exact_two_cover_of_adjoined_maximum`
- Dependency: [D5/S3/Topology/StableCategory/TrimmedAnchorMixedCone](TrimmedAnchorMixedCone.md)
