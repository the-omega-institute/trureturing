# Uniform soundness of original rays

## Abstract

Uniform soundness of original rays.

**Theorem 1.1 (Uniform soundness of original rays).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/RaySoundness.original_ray_gram_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/RaySoundness.original_ray_gram_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four disjoint identifier ranges together cover Fin 187. Their validity proofs supply the exact mass and Gram identities and the branch inequalities for every original label. The scalar envelope argument yields the Gram bound for arbitrary natural N at least 67 and every allowed middle position. Explicitly, the sum over a,b of gap(a) times gap(b) times min(position(a),position(b)) is bounded by bulkValue(N,bulkIndex(N)) times the square of the mass sum over a of gap(a) times position(a). This is the estimate used for the synthesized original rays.

These statements concern real scalar spectra and finite cofactor certificates. Connecting the boundary inequalities to a physical APPT model, constructing an attaining state, and determining a purity supremum require additional results.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/RaySoundness.original_ray_gram_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/LeadingRayCertificates](LeadingRayCertificates.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/MiddleRayCertificates](MiddleRayCertificates.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SparseRayCertificates](SparseRayCertificates.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/TrailingRayCertificates](TrailingRayCertificates.md)
