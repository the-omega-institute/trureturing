import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.ActiveCosineConstraints

/-! Dependence of tightness of the two lower moment bounds on the squared-mass objective. -/

namespace Reg.D5.S3.Fourier.Concentration.ActiveCosineConstraints

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.ActiveCosineConstraints
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => x ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {q : ℕ} [NeZero q] (_ : 4 ≤ q) {a : ℝ} (_ : 0 < a) (_ : a < 1),
    let c := fun k : ZMod q => Real.cos (2 * Real.pi * (k.val : ℝ) / q)
    let d := fun k : ZMod q => Real.cos (4 * Real.pi * (k.val : ℝ) / q)
    let square := V.readout () ()
    let probability := fun w : ZMod q → ℝ => (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1
    let moment := fun b w : ZMod q → ℝ => ∑ k, w k * b k
    let energy := fun w : ZMod q → ℝ => ∑ k, square (w k)
    let minimum := fun (F : (ZMod q → ℝ) → Prop) w =>
      F w ∧ ∀ v, F v → energy w ≤ energy v
    (∀ w, minimum (fun w => probability w ∧ a ≤ moment c w) w →
      moment c w = a ∧ moment d w < a) ∧
    (∀ w, minimum (fun w => probability w ∧ a ≤ moment d w) w →
      moment d w = a ∧ moment c w < a) ∧
    ∀ w, minimum (fun w => probability w ∧ a ≤ moment c w ∧ a ≤ moment d w) w →
      moment c w = a ∧ moment d w = a

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro law
  let w (k : ZMod 4) : ℝ := if k = 0 then 1 else 0
  have hnonneg (k : ZMod 4) : 0 ≤ w k := by
    simp only [w]
    split <;> norm_num
  have hmass : (∑ k, w k) = 1 := by simp [w]
  have hmoment :
      (∑ k : ZMod 4, w k * Real.cos (2 * Real.pi * (k.val : ℝ) / 4)) = 1 := by
    simp [w, ite_mul]
  have h := (law (q := 4) (by decide) (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).1
  have hmle :
      (1 / 2 : ℝ) ≤ ∑ k : ZMod 4, w k * Real.cos (2 * Real.pi * (k.val : ℝ) / 4) := by
    rw [hmoment]
    norm_num
  have hv := (h w ⟨⟨⟨hnonneg, hmass⟩, hmle⟩,
    fun v _ => by simp [rejected, realize]⟩).1
  change (∑ k : ZMod 4, w k * Real.cos (2 * Real.pi * (k.val : ℝ) / 4)) = 1 / 2 at hv
  rw [hmoment] at hv
  norm_num at hv

def evidence : Registration arena (type_of% @active_cosine_constraints) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@active_cosine_constraints, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℝ) ^ 2 ≠ (1 : ℝ) ^ 2
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@active_cosine_constraints) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.ActiveCosineConstraints.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.ActiveCosineConstraints.evidence
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
    owner := `D5.S3.Fourier.Concentration.ActiveCosineConstraints
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

end Reg.D5.S3.Fourier.Concentration.ActiveCosineConstraints
