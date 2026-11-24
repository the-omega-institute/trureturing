import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.DisjointCharacterEnvelope

/-! Dependence of the disjoint coefficient bound on the exponential coefficient norm. -/

namespace Reg.D5.S3.Fourier.Concentration.DisjointCharacterEnvelope

open Finset PowerSeries
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.DisjointCharacterEnvelope
open _root_.Reg.Support

noncomputable section
universe u

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ × ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => expTermNorm) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} (s : Finset J) (a b : J → ℂ) (m n : ℕ)
      (r : ℝ) (_ : 0 < r),
    let emptyPart := V.readout () ()
    ‖coeff n (coeff m (disjointSeries s a b))‖ ≤
      (emptyPart (r * ‖∑ j ∈ s, a j‖, m) * emptyPart (r * ‖∑ j ∈ s, b j‖, n) +
      Real.exp (r * (‖∑ j ∈ s, a j‖ + ‖∑ j ∈ s, b j‖)) *
        (∑ t ∈ overlapSubsets s m n,
          ∏ j ∈ t, (Real.exp (r * ‖a j‖) - 1) * (Real.exp (r * ‖b j‖) - 1))) /
        r ^ (m + n)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hzero := h (J := ULift.{u} Unit) ∅ (fun _ => 0) (fun _ => 0) 0 0 1 (by norm_num)
  have hOverlap : overlapSubsets (∅ : Finset (ULift.{u} Unit)) 0 0 = ∅ := by
    classical
    ext t
    simp [overlapSubsets]
  have hbad : (1 : ℝ) ≤ 0 := by
    simpa [rejected, realize, disjointSeries, hOverlap] using hzero
  norm_num at hbad

def evidence : Registration arena.{u} (type_of% @coefficient_envelope.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coefficient_envelope.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0, 1), (1, 1), ?_⟩
    change expTermNorm (0, 1) ≠ expTermNorm (1, 1)
    norm_num [expTermNorm]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@coefficient_envelope.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.DisjointCharacterEnvelope.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.DisjointCharacterEnvelope.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.DisjointCharacterEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.DisjointCharacterEnvelope
