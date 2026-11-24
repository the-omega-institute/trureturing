import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.ClippedMomentWeights

/-! Dependence of the squared-mass minimizer on the positive part of its affine weight. -/

namespace Reg.D5.S3.Fourier.Concentration.ClippedMomentWeights

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.ClippedMomentWeights
open _root_.Reg.Support

noncomputable section

universe u

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => max 0 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {ι : Type u} [Fintype ι] (c : ι → ℝ) {C a : ℝ}
      (hC : ∃ j, c j = C) (_ : a ≤ C),
    let positivePart := V.readout () ()
    let mean := (∑ i, c i) / Fintype.card ι
    let cutoff := univ.sup' (by obtain ⟨j, _⟩ := hC; exact ⟨j, mem_univ j⟩)
      (fun i => max 0 (C - c i)⁻¹)
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ cutoff ∧ (a ≤ mean → t = 0) ∧
      let u := fun i : ι => positivePart (1 - t * (C - c i))
      let v := fun i : ι => u i / ∑ j, u j
      (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = 1 ∧ (∑ i, v i * c i) = max mean a ∧
      ∀ w : ι → ℝ, (∑ i, w i) = 1 →
        let distance := ∑ i, (w i - v i) ^ 2
        let gap := (∑ i, w i ^ 2) - ∑ i, v i ^ 2
        let correction := t * ((∑ i, w i * c i) - ∑ i, v i * c i) +
          ∑ i, max 0 (t * (C - c i) - 1) * w i
        gap = distance + 2 * correction / (∑ i, u i) ∧
          ((∀ i, 0 ≤ w i) → a ≤ (∑ i, w i * c i) → distance ≤ gap)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  obtain ⟨t, _, _, _, _, hsum, _⟩ :=
    law (ι := ULift.{u} Unit) (fun _ => 0) (C := 0) (a := 0) ⟨ULift.up (), rfl⟩ le_rfl
  simp [rejected, realize] at hsum

def evidence : Registration arena.{u} (type_of% @exists_clipped_moment_minimizer.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_clipped_moment_minimizer.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.{u}.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change max (0 : ℝ) 0 ≠ max (0 : ℝ) 1
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@exists_clipped_moment_minimizer.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.ClippedMomentWeights.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.ClippedMomentWeights.evidence
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
    owner := `D5.S3.Fourier.Concentration.ClippedMomentWeights
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

end Reg.D5.S3.Fourier.Concentration.ClippedMomentWeights
