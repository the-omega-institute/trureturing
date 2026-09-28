# Four-cube coordinate geodesics

## Abstract

The Boolean four-cube has a sharp degree-two repair coefficient of two; the stronger exact matching-cost law remains open.

**Theorem 1.1 (Coordinate geodesic boundary).**

Lean statement: `D5/S3/Combinatorics/Graph/QuadripartiteH2Repair.geodesic_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/QuadripartiteH2Repair.geodesic_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four coordinate steps telescope in characteristic two, leaving the two endpoints.

**Theorem 1.2 (Coordinate geodesic weight).**

Lean statement: `D5/S3/Combinatorics/Graph/QuadripartiteH2Repair.geodesic_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/QuadripartiteH2Repair.geodesic_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each changed coordinate contributes exactly one supported triangular face.

**Theorem 1.3 (Sharp Boolean four-cube degree-two repair law).**

Lean statement: `D5/S3/Combinatorics/Graph/QuadripartiteH2Repair.universal_repair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/QuadripartiteH2Repair.universal_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural p and q, every triangular cochain admits an edge repair with q times repaired support at most p times its defect count exactly when 2*q <= p. The upper proof pairs the even defect set along coordinate geodesics, bounds the filling by twice its size, and uses local characteristic-two exactness; the antipodal witness proves sharpness.

The coefficient is optimal uniformly over all cochains. The theorem does not identify the minimum repair cost for each cochain.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2Repair.geodesic_boundary`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2Repair.geodesic_weight`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2Repair.universal_repair`
- Dependency: [D5/S3/Combinatorics/Graph/OctahedralCochainSharpness](OctahedralCochainSharpness.md)
- Dependency: [D5/S3/Combinatorics/Graph/TripartiteH1Repair](TripartiteH1Repair.md)
