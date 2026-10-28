import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition

open _root_.D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open MatrixMap
open scoped ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := ℂ × ℂ
  State _ := MatrixMap (Fin 3) (Fin 3) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ψ => (choi_matrix ψ).rank) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ α β : ℂ, ‖α‖ = 1 / Real.sqrt 2 → ‖β‖ = 1 / Real.sqrt 2 →
    ∃ (u : Matrix (Fin 3) (Fin 3) ℂ) (lam : ℝ)
      (ψ : MatrixMap (Fin 3) (Fin 3) ℂ),
      u ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧ 0 ≤ lam ∧ lam ≤ 1 ∧
      ψ.IsCompletelyPositive ∧ IsUnital ψ ∧ IsTracePreserving ψ ∧
      R.readout () (α, β) ψ = 3 ∧
      ψ ∈ Set.extremePoints ℝ
        {θ : MatrixMap (Fin 3) (Fin 3) ℂ | θ.IsCompletelyPositive ∧ IsUnital θ} ∧
      ψ ∈ Set.extremePoints ℝ
        {θ : MatrixMap (Fin 3) (Fin 3) ℂ |
          θ.IsCompletelyPositive ∧ IsTracePreserving θ} ∧
      ∀ ρ, hmrChannel α β ρ = (lam : ℂ) • (star u * ρ * u) +
        ((1 - lam : ℝ) : ℂ) • ψ ρ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hnorm : ‖(1 / Real.sqrt 2 : ℂ)‖ = 1 / Real.sqrt 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    positivity
  obtain ⟨u, lam, ψ, hu, hlam0, hlam1, hcp, hunit, htp, hrank, hue, hte, hdec⟩ :=
    h (1 / Real.sqrt 2) (1 / Real.sqrt 2) hnorm hnorm
  change (0 : ℕ) = 3 at hrank
  omega

theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hnorm : ‖(1 / Real.sqrt 2 : ℂ)‖ = 1 / Real.sqrt 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    positivity
  obtain ⟨u, lam, ψ, hu, hlam0, hlam1, hcp, hunit, htp, hrank, hue, hte, hdec⟩ :=
    result (1 / Real.sqrt 2) (1 / Real.sqrt 2) hnorm hnorm
  refine ⟨(1 / Real.sqrt 2, 1 / Real.sqrt 2), 0, ψ, ?_⟩
  change (choi_matrix (0 : MatrixMap (Fin 3) (Fin 3) ℂ)).rank ≠
    (choi_matrix ψ).rank
  rw [map_zero, Matrix.rank_zero, hrank]
  norm_num

def source_registration : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := by
    constructor
    · intro h α β hα hβ
      obtain ⟨u, lam, ψ, hu, hlam0, hlam1, hcp, hunit, htp, hrank, hue, hte, hdec⟩ :=
        h α β hα hβ
      exact ⟨u, lam, ψ, hu, hlam0, hlam1, hcp, hunit, htp, hrank, hue, hte, hdec⟩
    · intro h α β hα hβ
      obtain ⟨u, lam, ψ, hu, hlam0, hlam1, hcp, hunit, htp, hrank, hue, hte, hdec⟩ :=
        h α β hα hβ
      exact ⟨u, lam, ψ, hu, hlam0, hlam1, hcp, hunit, htp, hrank, hue, hte, hdec⟩
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ ψ => (choi_matrix ψ).rank) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition
