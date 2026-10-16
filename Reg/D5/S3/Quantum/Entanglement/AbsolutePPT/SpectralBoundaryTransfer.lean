import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN6PurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN7PurityBound

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction (K1 K2)
open LeanInformationAudit Matrix

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Fin (n + 10) → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ l => ∑ i, (l i) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

abbrev statement : Prop := ∀ (n a : ℕ), 1 ≤ a → SpectralBound n →
  SpectralBound (n + 1 + a) → SpectralBound (n + 1)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (n a : ℕ), 1 ≤ a → SpectralBound n → SpectralBound (n + 1 + a) →
    ∀ l : Fin (n + 10) → ℝ, Antitone l → (∀ i, 0 ≤ l i) →
      (∑ i, l i) = 1 → (K1 (boundaryValues (n + 1) l)).PosSemidef →
      (K2 (boundaryValues (n + 1) l)).PosSemidef →
      O.readout () n l ≤ purityBound (n + 10)

private theorem endpoint18 : SpectralBound 9 := by
  intro l ho hn ht h1 h2
  have hb : boundaryValues 9 l = QutritSpectralReduction.boundaryValues 3 l := by
    funext q
    fin_cases q <;> norm_num [boundaryValues, boundaryIndex, QutritSpectralReduction.boundaryValues]
  rw [hb] at h1 h2
  convert QutritN6PurityBound.certificate_bound l ho (hn 17) ht h1 h2 using 1 <;>
    norm_num [purityBound]

private theorem endpoint21 : SpectralBound 12 := by
  intro l ho hn ht h1 h2
  have hb : boundaryValues 12 l = QutritSpectralReduction.boundaryValues 4 l := by
    funext q
    fin_cases q <;> norm_num [boundaryValues, boundaryIndex, QutritSpectralReduction.boundaryValues]
  rw [hb] at h1 h2
  convert QutritN7PurityBound.certificate_bound l ho (hn 20) ht h1 h2 using 1 <;>
    norm_num [purityBound]

private theorem flat_psd (k : Bool) :
    ((if k then K1 else K2) (boundaryValues 10 (fun _ => (1 / 19 : ℝ)))).PosSemidef := by
  have heq : (if k then K1 else K2) (boundaryValues 10 (fun _ => (1 / 19 : ℝ))) =
      (2 / 19 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [K1, K2, boundaryValues, Matrix.smul_apply, Matrix.one_apply]
  rw [heq]
  exact Matrix.PosSemidef.one.smul (by norm_num)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hle := h 9 2 (by decide) endpoint18 endpoint21 (fun _ => (1 / 19 : ℝ))
    (fun _ _ _ => le_rfl) (fun _ => by norm_num) (by simp)
    (by simpa using flat_psd true) (by simpa using flat_psd false)
  norm_num [rejected, realize, purityBound] at hle

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  change (∑ _ : Fin 10, (0 : ℝ)^2) ≠ ∑ _ : Fin 10, (1 : ℝ)^2
  norm_num

def familyRegistration : Registration arena statement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨spectral_bound_transfer, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence

/-- The omitted source selector leaves the structural reconstruction obligation open. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.spectral_bound_transfer)
    (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.spectral_bound_transfer.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.familyRegistration,
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
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
