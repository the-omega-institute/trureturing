import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.Apollonian.CutoffOrderedSpectrum

namespace Reg.D5.S3.Combinatorics.Apollonian.CutoffOrderedSpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages
open _root_.D5.S3.Combinatorics.Apollonian.CutoffOrderedSpectrum
open LeanInformationAudit Matrix
noncomputable section
abbrev rootSignature : Signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def rootReadout : ∀ (_ : Unit) (_ : Unit), ℝ → ℝ := fun _ _ => Real.sqrt
abbrev actual : Realization rootSignature := realize rootSignature rootReadout (fun e => nomatch e)
abbrev spectrumArena : Arena where
  signature := rootSignature
  Law R := ∀ k t : ℕ,
    0 < (isHermitian_mul_conjTranspose_self (cutoffBlock k t)).eigenvalues₀ (secondIndex k) →
    cutoffSecond k t = R.readout () ()
      ((isHermitian_mul_conjTranspose_self (cutoffBlock k t)).eigenvalues₀ (secondIndex k))
private def bad : Realization rootSignature := realize rootSignature (fun _ _ _ => -1) (fun e => nomatch e)
private theorem bad_reject : ¬ spectrumArena.Law bad := by
  intro h
  have hp : 0 < (isHermitian_mul_conjTranspose_self (cutoffBlock 0 1)).eigenvalues₀ (secondIndex 0) := by
    norm_num [cutoffBlock, adjacency]
  have hh := h 0 1 hp
  rw [cutoff_second_eq_sqrt_gram 0 1 hp] at hh
  change Real.sqrt _ = -1 at hh
  have hn := Real.sqrt_nonneg
    ((isHermitian_mul_conjTranspose_self (cutoffBlock 0 1)).eigenvalues₀ (secondIndex 0))
  linarith

def cutoff_second_eq_sqrt_gram_family : Registration spectrumArena
    (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.CutoffOrderedSpectrum.cutoff_second_eq_sqrt_gram)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.CutoffOrderedSpectrum.cutoff_second_eq_sqrt_gram,
    bad, bad_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_reject
  dependence := by
    intro i; cases i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, rootReadout, realize]
def registration_cutoff_second_eq_sqrt_gram : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.CutoffOrderedSpectrum.cutoff_second_eq_sqrt_gram)
    (Realization rootSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.CutoffOrderedSpectrum.cutoff_second_eq_sqrt_gram_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.CutoffOrderedSpectrum.cutoff_second_eq_sqrt_gram_family
  realizationSource := none
  generated := false
  arena := .source ⟨spectrumArena⟩
  objectArena := .source ⟨spectrumArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source spectrumArena ⟨cutoff_second_eq_sqrt_gram_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rootSignature rootReadout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Combinatorics.Apollonian.CutoffOrderedSpectrum
