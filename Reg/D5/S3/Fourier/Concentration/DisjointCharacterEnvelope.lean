import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.DisjointCharacterEnvelope

/-! Dependence of the disjoint coefficient bound on the phase envelope. -/

namespace Reg.D5.S3.Fourier.Concentration.DisjointCharacterEnvelope

open Finset PowerSeries
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.DisjointCharacterEnvelope
open _root_.Reg.Support

noncomputable section
universe u

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => Real.exp) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} (s : Finset J) (a b : J → ℂ) (m n : ℕ)
      (r : ℝ) (_ : 0 < r),
    let phasePart := V.readout () ()
    ‖coeff n (coeff m (disjointSeries s a b))‖ ≤
      phasePart (r * (‖∑ j ∈ s, a j‖ + ‖∑ j ∈ s, b j‖)) *
        (∑ t ∈ overlapSubsets s m n,
          ∏ j ∈ t, (Real.exp (r * ‖a j‖) - 1) * (Real.exp (r * ‖b j‖) - 1)) /
        r ^ (m + n)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hzero := h (J := ULift.{u} Unit) ∅ (fun _ => 0) (fun _ => 0) 0 0 1 (by norm_num)
  have hbad : (1 : ℝ) ≤ 0 := by
    simpa [rejected, realize, disjointSeries, overlapSubsets] using hzero
  norm_num at hbad

def evidence : Registration arena.{u} (type_of% @coefficient_envelope.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coefficient_envelope.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change Real.exp 0 ≠ Real.exp 1
    exact ne_of_lt (Real.exp_lt_exp.mpr zero_lt_one)

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
