import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.CyclicFejerBand

/-! Dependence of the cyclic band bound on the squared norm of its window. -/

namespace Reg.D5.S3.Fourier.Concentration.CyclicFejerBand

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.CyclicFejerBand
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖ ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {q : ℕ} [NeZero q] (H N : ℕ) (_ : H < N) (M : ZMod q → ℝ)
      (_ : ∀ r, 0 ≤ M r),
    let windowWeight := V.readout () ()
    ((N - H : ℕ) : ℝ) * (∑ r ∈ band q H, M r) + H * M 0 ≤
      (∑ k : ZMod q, windowWeight (prefixCharacter q N k) *
        (ZMod.dft (fun r => (M r : ℂ)) k).re) / (q : ℝ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h (q := 1) 0 1 (by decide) (fun _ => 1) (by simp)
  have hfalse : (1 : ℝ) ≤ 0 := by simpa [rejected, realize, band] using hz
  norm_num at hfalse

def evidence : Registration arena (type_of% @band_le_positive_fourier) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@band_le_positive_fourier, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change ‖(0 : ℂ)‖ ^ 2 ≠ ‖(1 : ℂ)‖ ^ 2
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@band_le_positive_fourier) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CyclicFejerBand.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CyclicFejerBand.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.CyclicFejerBand
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.CyclicFejerBand
