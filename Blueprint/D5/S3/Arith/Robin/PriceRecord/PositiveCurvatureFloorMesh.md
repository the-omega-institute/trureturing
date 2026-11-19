# D5 source compiled; RegUNVALIDATED

## Abstract

PositiveCurvatureFloorMesh

The statements below concern the finite floor mesh and actual two/four cutoff curvature. They do not establish the complete paid-prefix repair or Robin inequality. RegUNVALIDATED: lawful registration, variation and source binding remain unfinished.

**Theorem 1.1 (positive_curvature_floor_mesh).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/PositiveCurvatureFloorMesh.positive_curvature_floor_mesh`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PositiveCurvatureFloorMesh.positive_curvature_floor_mesh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem positive_curvature_floor_mesh {α δ Δ : ℝ}     (hα : 0 < α) (hδ : 0 < δ) (hδα : δ < α)     (hΔ : 4 * α ^ 2 / δ + 2 * α ≤ Δ) :     let N : ℤ := ⌊Δ / α⌋; let r := Δ - ((N : ℝ) - 1) * α; ∃ A B : ℕ,       (B : ℤ) = ⌊r / δ⌋ - 1 ∧       (A : ℤ) = N - 1 - 2 * B ∧       (A : ℤ) + 2 * B = N - 1 ∧       (A + B : ℝ) ≤ Δ / α ∧       δ ≤ Δ - (A : ℝ) * α - (B : ℝ) * (2 * α + δ) ∧       Δ - (A : ℝ) * α - (B : ℝ) * (2 * α + δ) < 2 * δ

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PositiveCurvatureFloorMesh.positive_curvature_floor_mesh`
