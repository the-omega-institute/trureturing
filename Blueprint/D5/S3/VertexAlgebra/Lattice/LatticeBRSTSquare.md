# The full signed total BRST anomaly

## Abstract

The full signed total BRST anomaly

The original all-charge lattice carrier is tensored with the original bc occupation Fock space. The total charge is exactly the matter coupling plus the lifted cubic. Ghost degree two and commutation with every b and c mode force the actual square residual to vanish by the charged tensor commutant theorem, which applies to arbitrary matter modules. No scalar-vacuum argument on the matter tensor carrier is used.

**Theorem 1.1 (The full operator square).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTSquare.total_square_anomaly`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTSquare.total_square_anomaly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D : LatticeData, H : Matrix (Fin D.rank) (Fin D.rank) Complex, hHG : H * gramComplex D = 1 and hGH : gramComplex D * H = 1, (totalCharge D H)^2 = ((26-(D.rank : Complex))/26) smul ghostSquareAnomaly D. These two inverse-Gram identities are the only extra mathematical hypotheses. The anomaly is the actual lifted native ghost square, not an independently postulated certificate.

**Theorem 1.2 (Finite signed support on every tensor state).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTSquare.total_square_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTSquare.total_square_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D : LatticeData and x : State D, the function n : Int maps to (((D.rank : Complex)-26)/24 * ((n : Complex)^3-n)) smul ((ghostC D (-n) * ghostC D n) x) has finite support. Tensor induction extends pure-ghost support to arbitrary finite sums of simple tensors. This is statewise finiteness and makes no claim of finite support in the endomorphism space. No hypothesis on H or on a matter vacuum is used.

**Theorem 1.3 (The all-state all-integer signed formula).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTSquare.total_square_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTSquare.total_square_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D : LatticeData, H : Matrix (Fin D.rank) (Fin D.rank) Complex, hHG : H * gramComplex D = 1, hGH : gramComplex D * H = 1, and x : State D, ((totalCharge D H)^2) x equals the finite-support sum over all n : Int of (((D.rank : Complex)-26)/24 * ((n : Complex)^3-n)) smul ((ghostC D (-n) * ghostC D n) x). Scaling the native ghost coefficient -26/24 by (26-rank(D))/26 gives exactly (rank(D)-26)/24. At rank 26 the coefficient vanishes, so the original total charge squares to zero.

This algebraic result is a step toward the Monster, VOA/CFT, anomaly and fusion programme. BRST cohomology, the no-ghost theorem, a physical string model and an AdS/CFT correspondence require further constructions.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTSquare.total_square_anomaly`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTSquare.total_square_apply`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTSquare.total_square_finite`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard](LatticeBRSTWard.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree](LatticeMatterGhostDegree.md)
