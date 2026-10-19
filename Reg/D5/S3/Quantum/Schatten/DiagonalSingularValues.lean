import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Schatten.DiagonalSingularValues
import Reg.Support.SingleDependentReadout

/-! Full-source registration for the diagonal singular-value coordinates. -/
namespace Reg.D5.S3.Quantum.Schatten.DiagonalSingularValues
open _root_.D5.S3.Quantum.Schatten
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hh
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (a : Fin n → ℝ) (_ha : ∀ j, 0 ≤ a j)
    (σ : Equiv.Perm (Fin n)) (_hσ : Antitone (a ∘ σ))
    (i : Fin (Fintype.card (Fin n))),
    R.readout () () (singularValuesSorted (diagonal (fun j => (a j : ℂ))) i)
      (a (σ ⟨i.val, by simpa using i.isLt⟩))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 1 (fun _ => 0) (by simp) (Equiv.refl _) (by intro i j hij; exact le_rfl) ⟨0, by simp⟩
def source_registration : Registration arena
    (type_of% @singularValuesSorted_diagonal_of_antitone_perm) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@singularValuesSorted_diagonal_of_antitone_perm, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@singularValuesSorted_diagonal_of_antitone_perm) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.singularValuesSorted_diagonal_of_antitone_perm.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.DiagonalSingularValues.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.DiagonalSingularValues
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Schatten.DiagonalSingularValues
