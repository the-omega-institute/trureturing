import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.LatticeConvolutionVariance

/-! The score minorant and lattice-period readouts. -/

namespace Reg.D5.S3.Fourier.Concentration.LatticeConvolutionVariance

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.LatticeConvolutionVariance
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open _root_.D5.S3.Weil.DirichletPolynomialMeanSquare (phase)
open _root_.Reg.Support

noncomputable section
universe u

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def margin : Realization signature :=
  realize signature (fun _ _ x => max 0 (1-x/2)) (fun e => nomatch e)

def oversized : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private theorem margin_dependence : ObservationalDependence signature margin := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  norm_num [margin, realize]

namespace Score

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] (g w : J → ℝ), (∀ j, 0 ≤ w j) →
    ∀ (a V t : ℝ), (∑ j, w j * (g j - a)^2 ≤ V * ∑ j, w j) →
    let W := ∑ j, w j
    let margin := R.readout () ()
    W * margin (V*t^2) ≤ ‖complexScore g w t‖

private theorem rejected_law : ¬ arena.{u}.Law oversized := by
  intro h
  have hz := h (J := ULift.{u} Unit) (fun _ => 0) (fun _ => 1)
    (fun _ => zero_le_one) 0 0 0 (by simp)
  have hb : (2 : ℝ) ≤ 1 := by
    simpa [oversized, realize, complexScore, phase] using hz
  norm_num at hb

def evidence : Registration arena.{u} (type_of% @score_variance_lower.{u}) where
  actual := margin
  bridge := Iff.rfl
  variation := ⟨@score_variance_lower.{u}, oversized, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law margin oversized rejected_law
  dependence := margin_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@score_variance_lower.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.LatticeConvolutionVariance.Score.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.LatticeConvolutionVariance.Score.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature margin.readout margin.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.LatticeConvolutionVariance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Score

namespace Period

def actual : Realization signature :=
  realize signature (fun _ _ d => Real.pi/d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (a : J → ℤ) (b h : ℝ), 0 < h → ∀ (w : J → ℝ) (p : ℕ)
    (η : ℝ), 0 ≤ η → η < h →
    let g := fun j => b+h*(a j : ℝ)
    let period := R.readout () ()
    let A := period h
    intervalMean A (fun t => ‖complexScore g w t‖^(2*p)) =
      tailCollisionMass g w p η

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let a : ULift.{u} Unit → ℤ := fun _ => 0
  let w : ULift.{u} Unit → ℝ := fun _ => 1
  have hz := h a 0 1 zero_lt_one w 0 0 le_rfl zero_lt_one
  have ho := lattice_period_collision a 0 1 zero_lt_one w 0 0 le_rfl zero_lt_one
  have hc : tailCollisionMass (fun j => (0:ℝ)+1*(a j : ℝ)) w 0 0 = 1 := by
    rw [← ho]
    simp only [Nat.mul_zero, pow_zero]
    unfold intervalMean
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, div_one]
    field_simp [Real.pi_ne_zero]
    <;> ring
  dsimp only at hz
  rw [hc] at hz
  have hb : (0 : ℝ) = 1 := by
    simpa [rejected, realize, intervalMean] using hz
  norm_num at hb

def evidence : Registration arena.{u} (type_of% @lattice_period_collision.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lattice_period_collision.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change Real.pi/1 ≠ Real.pi/2
    intro he
    linarith [Real.pi_pos]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@lattice_period_collision.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.LatticeConvolutionVariance.Period.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.LatticeConvolutionVariance.Period.evidence
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
    owner := `D5.S3.Fourier.Concentration.LatticeConvolutionVariance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Period

namespace Collision

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (a : J → ℤ) (b h : ℝ), 0 < h → ∀ (w : J → ℝ), (∀ j, 0 ≤ w j) →
    ∀ (center V : ℝ) (p : ℕ) (η : ℝ), 0 ≤ η →
    (∑ j, w j * ((b + h * (a j : ℝ)) - center)^2 ≤ V * ∑ j, w j) →
    let g := fun j => b+h*(a j : ℝ)
    let W := ∑ j, w j
    let A := Real.pi/h
    let margin := R.readout () ()
    W^(2*p)*intervalMean A (fun t => (margin (V*t^2))^(2*p)) ≤
      tailCollisionMass g w p η

private theorem rejected_law : ¬ arena.{u}.Law oversized := by
  intro h
  let a : ULift.{u} Unit → ℤ := fun _ => 0
  let w : ULift.{u} Unit → ℝ := fun _ => 1
  have hz := h a 0 1 zero_lt_one w (by intro j; exact zero_le_one)
    0 0 1 0 le_rfl (by simp [a, w])
  have ho := lattice_period_collision a 0 1 zero_lt_one w 1 0 le_rfl zero_lt_one
  have hc : tailCollisionMass (fun j => (0:ℝ)+1*(a j : ℝ)) w 1 0 = 1 := by
    rw [← ho]
    simp [a, w, complexScore, phase, intervalMean, intervalIntegral.integral_const, smul_eq_mul]
    field_simp [Real.pi_ne_zero]
    <;> ring
  dsimp only at hz
  have hb : (4 : ℝ) ≤ 1 := by
    rw [hc] at hz
    simp [oversized, realize, w, intervalMean, intervalIntegral.integral_const, smul_eq_mul] at hz
    have he : Real.pi⁻¹ * 2⁻¹ * ((Real.pi + Real.pi) * 2^2) = 4 := by
      field_simp [Real.pi_ne_zero]
      <;> ring
    rw [he] at hz
    exact hz
  norm_num at hb

def evidence : Registration arena.{u} (type_of% @lattice_collision_variance_lower.{u}) where
  actual := margin
  bridge := Iff.rfl
  variation := ⟨@lattice_collision_variance_lower.{u}, oversized, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law margin oversized rejected_law
  dependence := margin_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@lattice_collision_variance_lower.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.LatticeConvolutionVariance.Collision.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.LatticeConvolutionVariance.Collision.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature margin.readout margin.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.LatticeConvolutionVariance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Collision

end

end Reg.D5.S3.Fourier.Concentration.LatticeConvolutionVariance
