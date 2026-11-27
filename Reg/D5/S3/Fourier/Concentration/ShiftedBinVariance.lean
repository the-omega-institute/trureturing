import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.ShiftedBinVariance

/-! Dependence on the rounding penalty and the squared norm of the parabolic test. -/

namespace Reg.D5.S3.Fourier.Concentration.ShiftedBinVariance

open Finset Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.ShiftedBinVariance
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open _root_.Reg.Support

noncomputable section
universe u

namespace Rounding

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => fun x : ℝ => Int.fract x * (1 - Int.fract x)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law U := ∀ {I : Type u} (s : Finset I) (z c : I → ℝ),
    let roundingPenalty := U.readout () ()
    ∃ u ∈ Ico (0 : ℝ) 1,
      (∑ i ∈ s, c i * (⌊z i + u⌋ : ℝ) ^ 2) ≤
        ∑ i ∈ s, c i * ((z i) ^ 2 + roundingPenalty (z i))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨v, hv, hbad⟩ := h (I := ULift.{u} Unit) {ULift.up ()} (fun _ => 0) (fun _ => 1)
  have hfalse : (⌊v⌋ : ℝ)^2 ≤ -1 := by
    simpa [rejected, realize] using hbad
  nlinarith [sq_nonneg (⌊v⌋ : ℝ)]

def evidence : Registration arena.{u} (type_of% @exists_shifted_squared_moment.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_shifted_squared_moment.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1/2 : ℝ), ?_⟩
    change Int.fract (0 : ℝ) * (1 - Int.fract 0) ≠ Int.fract (1/2 : ℝ) * (1 - Int.fract (1/2))
    have h : Int.fract (1/2 : ℝ) = 1/2 := Int.fract_eq_self.mpr (by norm_num)
    rw [h, Int.fract_zero]
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@exists_shifted_squared_moment.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.ShiftedBinVariance.Rounding.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.ShiftedBinVariance.Rounding.evidence
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
    owner := `D5.S3.Fourier.Concentration.ShiftedBinVariance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Rounding

namespace Parabola

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => 16 * (n : ℝ) / 15 - 1 / (15 * (n : ℝ) ^ 3))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law U := ∀ {I : Type u} (s : Finset I) (x c : I → ℝ) (a V η : ℝ)
    (_ : 0 < η) (_ : ∀ i ∈ s, 0 ≤ c i)
    (_ : ∑ i ∈ s, c i * (x i - a)^2 ≤ V * ∑ i ∈ s, c i)
    (r : ℕ) (_ : 0 < r) (_ : V / η^2 + 1/4 ≤ (r : ℝ)^2),
    let W := ∑ i ∈ s, c i
    let M := V / η ^ 2 + 1 / 4
    let factor := U.readout () ()
    W ^ 2 * (1 - M / (r : ℝ) ^ 2) ^ 2 ≤
      factor r * nearCollisionMass s x c η

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := h (I := ULift.{u} Unit) {ULift.up ()} (fun _ => 0) (fun _ => 1)
    0 0 1 (by norm_num) (by simp) (by norm_num) 1 (by decide) (by norm_num)
  have hfalse : (1 : ℝ)^2 * (1 - (0/1^2+1/4)/1^2)^2 ≤
      0 * nearCollisionMass ({ULift.up ()} : Finset (ULift.{u} Unit)) (fun _ => 0) (fun _ => 1) 1 := by
    simpa only [arena, rejected, realize, Finset.sum_singleton, Nat.cast_one] using hz
  norm_num at hfalse

def evidence : Registration arena.{u} (type_of% @collision_parabolic_lower.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@collision_parabolic_lower.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@collision_parabolic_lower.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.ShiftedBinVariance.Parabola.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.ShiftedBinVariance.Parabola.evidence
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
    owner := `D5.S3.Fourier.Concentration.ShiftedBinVariance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Parabola

end

end Reg.D5.S3.Fourier.Concentration.ShiftedBinVariance
