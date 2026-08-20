/- GID: D5/S3/ObserverMemory/InverseLimits/DiagonalCornerReconstruction
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/InverseLimits/DiagonalCornerReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Coordinate corners recover every transition of a transfer operator. -/

import D5.S3.ObserverMemory.InverseLimits.TraceRankCombinatorics

/- Library-search audit trail (2026-08-20):
   * The imported repository module supplies the exact source transfer operator,
     constructed as `Finsupp.lmapDomain` and characterized on basis vectors.
   * Pinned Mathlib supplies exact hits `Finsupp.lapply_comp_lsingle_same`,
     `Finsupp.lapply_comp_lsingle_of_ne`, `Finsupp.lmapDomain_apply`,
     `Finsupp.mapDomain_single`, `Finsupp.lsingle_apply`, and
     `Finsupp.lapply_apply`; they are applied below.
   * Repository and pinned-Mathlib shape searches found no theorem packaging the
     nonzero corner criterion together with both exact action clauses. -/

noncomputable section

namespace D5.S3.ObserverMemory.InverseLimits.DiagonalCornerReconstruction

open D5.S3.ObserverMemory.InverseLimits.TraceRankCombinatorics

/-- The coordinate basis vector constructed from a state. -/
def basisVector {Y : Type*} (y : Y) : Finsupp Y Complex :=
  Finsupp.single y 1

/-- Projection onto the coordinate line at a state. -/
def coordinateProjection {Y : Type*} (y : Y) :
    Module.End Complex (Finsupp Y Complex) :=
  (Finsupp.lsingle y).comp (Finsupp.lapply y)

/-- The coordinate corner obtained by projecting before and after transfer. -/
def diagonalCorner {Y : Type*} (z : Y) (tau : Y -> Y) (y : Y) :
    Module.End Complex (Finsupp Y Complex) :=
  (coordinateProjection z).comp
    ((transferOperator tau).comp (coordinateProjection y))

private theorem coordinate_projection_single_same {Y : Type*} (y : Y)
    (c : Complex) :
    coordinateProjection y (Finsupp.single y c) = Finsupp.single y c := by
  have hsame :
      (Finsupp.lapply y : Finsupp Y Complex →ₗ[Complex] Complex)
          ((Finsupp.lsingle y : Complex →ₗ[Complex] Finsupp Y Complex) c) = c :=
    LinearMap.congr_fun
      (Finsupp.lapply_comp_lsingle_same (R := Complex) (M := Complex) y) c
  change Finsupp.single y
    ((Finsupp.lapply y : Finsupp Y Complex →ₗ[Complex] Complex)
      (Finsupp.single y c)) = Finsupp.single y c
  simpa only [Finsupp.lsingle_apply] using
    congrArg (fun a : Complex => Finsupp.single y a) hsame

private theorem coordinate_projection_single_of_ne {Y : Type*} {z w : Y}
    (hzw : z ≠ w) (c : Complex) :
    coordinateProjection z (Finsupp.single w c) = 0 := by
  have hzero :
      (Finsupp.lapply z : Finsupp Y Complex →ₗ[Complex] Complex)
          ((Finsupp.lsingle w : Complex →ₗ[Complex] Finsupp Y Complex) c) = 0 :=
    LinearMap.congr_fun
      (Finsupp.lapply_comp_lsingle_of_ne (R := Complex) (M := Complex)
        z w hzw) c
  change Finsupp.single z
    ((Finsupp.lapply z : Finsupp Y Complex →ₗ[Complex] Complex)
      (Finsupp.single w c)) = 0
  simpa only [Finsupp.lsingle_apply, Finsupp.single_zero] using
    congrArg (fun a : Complex => Finsupp.single z a) hzero

private theorem transfer_operator_single {Y : Type*} (tau : Y -> Y)
    (y : Y) (c : Complex) :
    transferOperator tau (Finsupp.single y c) = Finsupp.single (tau y) c := by
  rw [transferOperator, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

private theorem coordinate_projection_apply {Y : Type*} (y : Y)
    (v : Finsupp Y Complex) :
    coordinateProjection y v = Finsupp.single y (v y) := by
  rfl

private theorem diagonal_corner_basis_action_of_eq {Y : Type*}
    (tau : Y -> Y) (y z : Y) (hz : z = tau y) :
    diagonalCorner z tau y (basisVector y) = basisVector z := by
  subst z
  rw [diagonalCorner, LinearMap.comp_apply, LinearMap.comp_apply,
    basisVector, coordinate_projection_single_same, transfer_operator_single,
    coordinate_projection_single_same]
  rfl

private theorem diagonal_corner_eq_zero_of_ne {Y : Type*}
    (tau : Y -> Y) (y z : Y) (hz : z ≠ tau y) :
    diagonalCorner z tau y = 0 := by
  apply LinearMap.ext
  intro v
  rw [diagonalCorner, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [coordinate_projection_apply y v]
  rw [transfer_operator_single]
  rw [coordinate_projection_single_of_ne hz]
  rfl

/-- Every transfer arrow is recovered by its diagonal coordinate corner: the
corner is nonzero exactly on that arrow, acts on its source basis vector as
claimed, and is the zero operator away from the arrow. -/
theorem diagonal_corner_reconstruction {Y : Type*} (tau : Y -> Y) (y z : Y) :
    (diagonalCorner z tau y ≠ 0 ↔ z = tau y) ∧
    (z = tau y →
      diagonalCorner z tau y (basisVector y) = basisVector z) ∧
    (z ≠ tau y → diagonalCorner z tau y = 0) := by
  constructor
  · constructor
    · intro hcorner
      by_contra hz
      exact hcorner (diagonal_corner_eq_zero_of_ne tau y z hz)
    · intro hz hzero
      have haction := diagonal_corner_basis_action_of_eq tau y z hz
      rw [hzero] at haction
      have hbasis : basisVector z ≠ 0 := by
        rw [basisVector, Finsupp.single_ne_zero]
        exact one_ne_zero
      exact hbasis haction.symm
  · exact
      ⟨diagonal_corner_basis_action_of_eq tau y z,
        diagonal_corner_eq_zero_of_ne tau y z⟩

/-- The theorem's state type may be a singleton. -/
example : Nonempty (Fin 1) := ⟨0⟩

/-- The identity transfer realizes a concrete nonzero corner. -/
example : diagonalCorner 0 (fun x : Fin 1 => x) 0 ≠ 0 := by
  exact (diagonal_corner_reconstruction (fun x : Fin 1 => x) 0 0).1.2 rfl

#print axioms diagonal_corner_reconstruction

end D5.S3.ObserverMemory.InverseLimits.DiagonalCornerReconstruction
