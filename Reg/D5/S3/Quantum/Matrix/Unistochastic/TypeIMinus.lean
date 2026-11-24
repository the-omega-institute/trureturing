import D5.S3.Quantum.Matrix.Unistochastic.TypeIMinus
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The readout tests an individual Hadamard coordinate for nonnegativity. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix.Unistochastic.TypeIMinus
open Matrix

namespace Reg.D5.S3.Quantum.Matrix.Unistochastic.TypeIMinus

noncomputable section

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law A := ∀ (U : Matrix (Fin 4) (Fin 4) ℂ), U ∈ Matrix.unitaryGroup (Fin 4) ℂ →
    ∃ i j : Fin 3, A.readout () () ((Hᵀ * RHLinalg.normSqMatrix U * H) i j)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, hf⟩ := h 1 (Matrix.unitaryGroup (Fin 4) ℂ).one_mem
  exact hf

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), -1, ?_⟩
  intro h
  change (0 ≤ (0 : ℝ)) = (0 ≤ (-1 : ℝ)) at h
  have hf := Eq.mp h (le_refl (0 : ℝ))
  norm_num at hf

def family : Registration arena (type_of% @exists_nonneg_typeIMinus) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_nonneg_typeIMinus, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_nonneg_typeIMinus) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Matrix.Unistochastic.TypeIMinus.exists_nonneg_typeIMinus.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.Unistochastic.TypeIMinus.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.Unistochastic.TypeIMinus
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Matrix.Unistochastic.TypeIMinus
