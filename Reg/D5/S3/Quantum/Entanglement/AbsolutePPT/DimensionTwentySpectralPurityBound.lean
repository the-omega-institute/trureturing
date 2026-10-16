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

abbrev sharpStatement : Prop := IsGreatest
  {p : ℝ | ∃ l : Fin 20 → ℝ, Antitone l ∧ (∀ i, 0 ≤ l i) ∧ (∑ i, l i) = 1 ∧
    (K1 (boundaryValues 11 l)).PosSemidef ∧ (K2 (boundaryValues 11 l)).PosSemidef ∧
      (∑ i, (l i) ^ 2) = p} (7 / 121 : ℝ)

abbrev sharpArena : Arena where
  signature := signature
  Law O := IsGreatest
    {p : ℝ | ∃ l : Fin 20 → ℝ, Antitone l ∧ (∀ i, 0 ≤ l i) ∧ (∑ i, l i) = 1 ∧
      (K1 (boundaryValues 11 l)).PosSemidef ∧ (K2 (boundaryValues 11 l)).PosSemidef ∧
        O.readout () () l = p} (7 / 121 : ℝ)

private theorem rejected_bound : ¬ boundArena.Law rejected := by
  intro h
  obtain ⟨l, ho, hn, ht, h1, h2, _⟩ := sharp_spectral_purity_bound.1
  have hle := h l ho hn ht h1 h2
  norm_num [rejected, realize] at hle

private theorem rejected_sharp : ¬ sharpArena.Law rejected := by
  intro h
  obtain ⟨l, _, _, _, _, _, heq⟩ := h.1
  norm_num [rejected, realize] at heq

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun j => if j = 0 then 1 else 0), ?_⟩
  norm_num [actual, realize, Fin.sum_univ_succ]

def boundFamilyRegistration : Registration boundArena boundStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨spectral_purity_bound, rejected, rejected_bound⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity boundArena.Law actual rejected rejected_bound
  dependence := actual_dependence

def sharpFamilyRegistration : Registration sharpArena sharpStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sharp_spectral_purity_bound, rejected, rejected_sharp⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity sharpArena.Law actual rejected rejected_sharp
  dependence := actual_dependence

/-- The omitted source selector leaves the structural reconstruction obligation open. -/
def boundRegistration : Contract.Registration
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
  escapeFrom := some (Fin 20 → ℝ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

/-- The omitted source selector leaves the structural reconstruction obligation open. -/
def sharpRegistration : Contract.Registration
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound.sharp_spectral_purity_bound)
    (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound.sharp_spectral_purity_bound.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound.sharpFamilyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨sharpArena⟩,
  objectArena := .source ⟨sharpArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source sharpArena ⟨sharpFamilyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ l => ∑ i, (l i) ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (Fin 20 → ℝ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound
