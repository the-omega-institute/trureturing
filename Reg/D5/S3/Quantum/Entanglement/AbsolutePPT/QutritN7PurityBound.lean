import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN7PurityBound

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN7PurityBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction
open LeanInformationAudit Matrix

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 21 → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ l => ∑ i, (l i) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

abbrev statement : Prop := ∀ l : Fin 21 → ℝ, Antitone l → 0 ≤ l 20 →
  (∑ i, l i) = 1 → (K1 (boundaryValues 4 l)).PosSemidef →
    (K2 (boundaryValues 4 l)).PosSemidef → ∑ i, (l i) ^ 2 ≤ (29 : ℝ) / 23 ^ 2

abbrev arena : Arena where
  signature := signature
  Law O := ∀ l : Fin 21 → ℝ, Antitone l → 0 ≤ l 20 →
    (∑ i, l i) = 1 → (K1 (boundaryValues 4 l)).PosSemidef →
      (K2 (boundaryValues 4 l)).PosSemidef → O.readout () () l ≤ (29 : ℝ) / 23 ^ 2

private theorem flat_psd (k : Bool) :
    ((if k then K1 else K2) (boundaryValues 4 (fun _ => (1 / 21 : ℝ)))).PosSemidef := by
  have heq : (if k then K1 else K2) (boundaryValues 4 (fun _ => (1 / 21 : ℝ))) =
      (2 / 21 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [K1, K2, boundaryValues, Matrix.smul_apply, Matrix.one_apply]
  rw [heq]
  exact Matrix.PosSemidef.one.smul (by norm_num)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hle := h (fun _ => (1 / 21 : ℝ)) (fun _ _ _ => le_rfl) (by norm_num)
    (by simp) (by simpa using flat_psd true) (by simpa using flat_psd false)
  change (2 : ℝ) ≤ 29 / 23^2 at hle
  norm_num at hle

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  change (∑ _ : Fin 21, (0 : ℝ)^2) ≠ ∑ _ : Fin 21, (1 : ℝ)^2
  norm_num

def familyRegistration : Registration arena statement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN7PurityBound.certificate_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence

/-- Source selection retains the complete spectral telescope and its square-sum observation. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN7PurityBound.certificate_bound)
    (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN7PurityBound.certificate_bound.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN7PurityBound.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ l => ∑ i, (l i) ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN7PurityBound,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN7PurityBound
