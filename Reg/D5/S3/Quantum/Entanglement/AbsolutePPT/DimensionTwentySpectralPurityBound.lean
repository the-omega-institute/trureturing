import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction (K1 K2)
open LeanInformationAudit Matrix

noncomputable section

open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 20 → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ l => ∑ i, (l i) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

abbrev boundStatement : Prop := ∀ l : Fin 20 → ℝ, Antitone l →
  (∀ i, 0 ≤ l i) → (∑ i, l i) = 1 → (K1 (boundaryValues 11 l)).PosSemidef →
    (K2 (boundaryValues 11 l)).PosSemidef → ∑ i, (l i) ^ 2 ≤ (7 / 121 : ℝ)

abbrev boundArena : Arena where
  signature := signature
  Law O := ∀ l : Fin 20 → ℝ, Antitone l → (∀ i, 0 ≤ l i) → (∑ i, l i) = 1 →
    (K1 (boundaryValues 11 l)).PosSemidef → (K2 (boundaryValues 11 l)).PosSemidef →
      O.readout () () l ≤ (7 / 121 : ℝ)

private theorem rejected_bound : ¬ boundArena.Law rejected := by
  intro h
  let l : Fin 20 → ℝ := fun _ => 1 / 20
  have hpsd (k : Bool) :
      ((if k then K1 else K2) (boundaryValues 11 l)).PosSemidef := by
    have heq : (if k then K1 else K2) (boundaryValues 11 l) =
        (1 / 10 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
      cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [K1, K2, boundaryValues, l, Matrix.smul_apply, Matrix.one_apply]
    rw [heq]
    exact Matrix.PosSemidef.one.smul (by norm_num)
  have hle := h l (fun _ _ _ => le_rfl) (fun _ => by norm_num [l])
    (by simp [l]) (by simpa using hpsd true) (by simpa using hpsd false)
  change (2 : ℝ) ≤ 7 / 121 at hle
  norm_num at hle

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  change (∑ _ : Fin 20, (0 : ℝ)^2) ≠ ∑ _ : Fin 20, (1 : ℝ)^2
  norm_num

def boundFamilyRegistration : Registration boundArena boundStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨spectral_purity_bound, rejected, rejected_bound⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity boundArena.Law actual rejected rejected_bound
  dependence := actual_dependence

/-- Source selection retains the complete spectral telescope and its square-sum observation. -/
def boundRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound.spectral_purity_bound)
    (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound.spectral_purity_bound.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound.boundFamilyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨boundArena⟩,
  objectArena := .source ⟨boundArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source boundArena ⟨boundFamilyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ l => ∑ i, (l i) ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound
