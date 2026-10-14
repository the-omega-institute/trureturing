/- GID: D5/S3/VertexAlgebra/TensorConformal/LatticeBcGhostStressBoundary
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TensorConformal/LatticeBcGhostStressBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual stress and translation boundaries for the original full tensor BRST charge. -/

import D5.S3.VertexAlgebra.TensorConformal.LatticeBcGhostTotalConformal
import D5.S3.VertexAlgebra.LatticeBcGhostBrstCurrent
import D5.S3.VertexAlgebra.LatticeBcGhostBrstNilpotence

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TensorConformal.LatticeBcGhostStressBoundary

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
open LatticeBcGhostTotalConformal
open scoped TensorProduct VertexOperator

noncomputable section

theorem cycle_mode_boundary (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ) (psi : State D)
    (cycle : Q D H psi = 0) :
    totalMode D H mode psi = Q D H (B D mode psi) ∧
      totalMode D H mode psi ∈ LinearMap.range (Q D H) ∧
      ((LatticeBcGhostTensorStateField.stateField D (omega D H))[[mode + 1]]) psi =
        Q D H (B D mode psi) ∧
      ((LatticeBcGhostTensorStateField.stateField D (omega D H))[[mode + 1]]) psi ∈
        LinearMap.range (Q D H) := by
  have ward := congrArg (fun operator : Module.End ℂ (State D) => operator psi)
    (ward_identity D H mode)
  have boundary : totalMode D H mode psi = Q D H (B D mode psi) := by
    simpa only [LinearMap.add_apply, Module.End.mul_apply, cycle, map_zero,
      add_zero, totalMode] using ward.symm
  have member : totalMode D H mode psi ∈ LinearMap.range (Q D H) :=
    ⟨B D mode psi, boundary.symm⟩
  have coefficient :
      (LatticeBcGhostTensorStateField.stateField D (omega D H))[[mode + 1]] =
        totalMode D H mode := omega_modes D H mode
  rw [coefficient]
  exact ⟨boundary, member, boundary, member⟩

theorem omega_boundary (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    omega D H = Q D H (B D (-2) (LatticeBcGhostTensorStateField.vacuum D)) ∧
      omega D H ∈ LinearMap.range (Q D H) := by
  have vacuumCycle : Q D H (LatticeBcGhostTensorStateField.vacuum D) = 0 :=
    LatticeBcGhostBrstCurrent.Q_vacuum D H
  have boundary := cycle_mode_boundary D H (-2)
    (LatticeBcGhostTensorStateField.vacuum D) vacuumCycle
  rw [omega_creation] at boundary
  exact ⟨boundary.1, boundary.2.1⟩

theorem cycle_translation_boundary (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (psi : State D) (cycle : Q D H psi = 0) :
    LatticeBcGhostTensorStateField.translation D psi = Q D H (B D (-1) psi) ∧
      LatticeBcGhostTensorStateField.translation D psi ∈ LinearMap.range (Q D H) := by
  have boundary := cycle_mode_boundary D H (-1) psi cycle
  rw [minus_one_eq_translation D H leftInverse rightInverse] at boundary
  exact ⟨boundary.1, boundary.2.1⟩

theorem critical_cycle_preservation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (critical : D.rank = 26) :
    Q D H (omega D H) = 0 ∧
      (∀ (mode : ℤ) (psi : State D), Q D H psi = 0 →
        Q D H (totalMode D H mode psi) = 0 ∧
          Q D H (((LatticeBcGhostTensorStateField.stateField D
            (omega D H))[[mode + 1]]) psi) = 0) ∧
      (∀ psi : State D, Q D H psi = 0 →
        Q D H (LatticeBcGhostTensorStateField.translation D psi) = 0) := by
  have square := LatticeBcGhostBrstNilpotence.nilpotent D H
    leftInverse rightInverse critical
  have stressCycle : Q D H (omega D H) = 0 := by
    rw [(omega_boundary D H).1]
    have evaluated := congrArg (fun operator : Module.End ℂ (State D) =>
      operator (B D (-2) (LatticeBcGhostTensorStateField.vacuum D))) square
    exact evaluated
  have modeCycle (mode : ℤ) (psi : State D) (cycle : Q D H psi = 0) :
      Q D H (totalMode D H mode psi) = 0 := by
    have covariance := congrArg (fun operator : Module.End ℂ (State D) => operator psi)
      (LatticeBcGhostBrstTotalCovariance.total_covariance D H
        leftInverse rightInverse mode)
    simpa [critical, cycle, totalMode, Module.End.mul_apply] using covariance
  refine ⟨stressCycle, ?_, ?_⟩
  · intro mode psi cycle
    refine ⟨modeCycle mode psi cycle, ?_⟩
    rw [omega_modes]
    exact modeCycle mode psi cycle
  · intro psi cycle
    rw [← minus_one_eq_translation D H leftInverse rightInverse]
    exact modeCycle (-1) psi cycle

end

end D5.S3.VertexAlgebra.TensorConformal.LatticeBcGhostStressBoundary
