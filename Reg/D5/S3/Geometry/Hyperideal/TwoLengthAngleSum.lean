import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
import Reg.Support.DependentFamily
import Reg.D5.S3.Geometry.Hyperideal.NativeRadicand

open scoped BigOperators
open _root_.D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
open _root_.D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open _root_.D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
noncomputable section

-- Sigma is the interface's exact packing of the two original real binders.
abbrev signature : Signature where
  Params := Σ A : ℝ, ℝ
  State _ := Finset (Fin 6)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p S => ∑ q ∈ S,
    extendedAngle (fun j => if j ∈ S then p.2 else p.1) q)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

-- All original parameters, hypotheses and multiplicities stay in the law.
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A B : ℝ) (hA : 1 < A) (hB : 4*A+5 < B)
    (S : Finset (Fin 6)) (hS : 2 ≤ S.card),
    (S.card : ℝ)*Real.pi/4 < R.readout () ⟨A, B⟩ S

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 14 (by norm_num) (by norm_num)
    (Finset.univ : Finset (Fin 6)) (by decide)
  change ((Finset.univ : Finset (Fin 6)).card : ℝ)*Real.pi/4 < 0 at hh
  have hc : ((Finset.univ : Finset (Fin 6)).card : ℝ) = 6 := by norm_num
  rw [hc] at hh
  linarith [Real.pi_pos]

private def opposite : Finset (Fin 6) := {0, 3}
private def oppositeValues : Fin 6 → ℝ :=
  fun j => if j ∈ opposite then 14 else 2

private theorem opposite_calculation : ∀ q ∈ opposite,
    rawNum oppositeValues q = -2610 ∧ leftRad oppositeValues q = 315 ∧
      rightRad oppositeValues q = 315 := by
  intro q hq
  have hq' : q = 0 ∨ q = 3 := by simpa [opposite] using hq
  rcases hq' with rfl | rfl
  all_goals
    simp only [rawNum, leftRad, rightRad, oppositeValues, opposite, frame,
      Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;>
      norm_num

private theorem opposite_angles : ∀ q ∈ opposite,
    extendedAngle oppositeValues q = Real.pi := by
  intro q hq
  obtain ⟨hn, hl, hr⟩ := opposite_calculation q hq
  have hc : rawCos oppositeValues q = (-2610/315 : ℝ) := by
    change rawNum oppositeValues q / Real.sqrt (leftRad oppositeValues q) /
      Real.sqrt (rightRad oppositeValues q) = _
    rw [hn, hl, hr, div_div, ← pow_two,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 315)]
  unfold extendedAngle
  rw [hc]
  norm_num [Real.arccos_neg_one]

private theorem opposite_readout (i : Unit) :
    actual.readout i ⟨2, 14⟩ opposite = 2*Real.pi := by
  change (∑ q ∈ opposite, extendedAngle oppositeValues q) = _
  calc
    _ = ∑ _q ∈ opposite, Real.pi := Finset.sum_congr rfl opposite_angles
    _ = 2*Real.pi := by norm_num [opposite, nsmul_eq_mul, Fin.ext_iff]

private theorem regular_cosine (q : Fin 6) :
    rawCos (fun _ => 14) q = (14/27 : ℝ) := by
  change cosine 14 14 14 14 14 14 = _
  have hn : numerator 14 14 14 14 14 14 = (3150 : ℝ) := by norm_num [numerator]
  have hr : rad 14 14 14 = (6075 : ℝ) := by norm_num [rad]
  rw [cosine, hn, hr, div_div, ← pow_two,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6075)]
  norm_num

private theorem regular_angle (q : Fin 6) :
    extendedAngle (fun _ => 14) q = Real.arccos (14/27 : ℝ) := by
  unfold extendedAngle
  rw [regular_cosine]
  norm_num

private theorem full_readout (i : Unit) :
    actual.readout i ⟨2, 14⟩ Finset.univ = 6*Real.arccos (14/27 : ℝ) := by
  change (∑ q ∈ (Finset.univ : Finset (Fin 6)),
    extendedAngle (fun j => if j ∈ (Finset.univ : Finset (Fin 6)) then 14 else 2) q) = _
  simp only [Finset.mem_univ, if_true]
  simp [regular_angle, nsmul_eq_mul]

private theorem full_readout_lt (i : Unit) :
    actual.readout i ⟨2, 14⟩ Finset.univ < 2*Real.pi := by
  have ha : Real.arccos (14/27 : ℝ) < Real.pi/3 := by
    have h := Real.arccos_lt_arccos (Real.neg_one_le_cos (Real.pi/3))
      (by norm_num [Real.cos_pi_div_three] : Real.cos (Real.pi/3) < (14/27 : ℝ))
      (by norm_num : (14/27 : ℝ) ≤ 1)
    rw [Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])] at h
    exact h
  rw [full_readout]
  linarith

def registration : Registration arena
    (type_of% (@_root_.D5.S3.Geometry.Hyperideal.TwoLengthAngleSum.two_length_angle_sum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Geometry.Hyperideal.TwoLengthAngleSum.two_length_angle_sum,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨2, 14⟩, opposite, Finset.univ, ?_⟩
    intro he
    have h := full_readout_lt i
    rw [← he, opposite_readout] at h
    exact (lt_irrefl _ h)

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.Hyperideal.TwoLengthAngleSum.two_length_angle_sum)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ p S => ∑ q ∈ S,
        extendedAngle (fun j => if j ∈ S then p.2 else p.1) q)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Hyperideal.TwoLengthAngleSum.two_length_angle_sum.sum_unit,
  realizationName := `Reg.D5.S3.Geometry.Hyperideal.TwoLengthAngleSum.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ p S => ∑ q ∈ S,
      extendedAngle (fun j => if j ∈ S then p.2 else p.1) q)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Geometry.Hyperideal.TwoLengthAngleSum, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1

noncomputable def registration_2 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.Hyperideal.TwoLengthAngleSum.rad_positive)
    (type_of% (realize.{0,0,0,0,0}
      _root_.Reg.D5.S3.Geometry.Hyperideal.NativeRadicand.signature
      (fun _ p z => rad p.1 p.2 z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Hyperideal.TwoLengthAngleSum.rad_positive.native_radicand_unit
  realizationName := `Reg.D5.S3.Geometry.Hyperideal.NativeRadicand.radicand_family
  realizationSource := none
  generated := false
  arena := .source ⟨_root_.Reg.D5.S3.Geometry.Hyperideal.NativeRadicand.arena⟩
  objectArena := .source ⟨_root_.Reg.D5.S3.Geometry.Hyperideal.NativeRadicand.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source _root_.Reg.D5.S3.Geometry.Hyperideal.NativeRadicand.arena
    ⟨_root_.Reg.D5.S3.Geometry.Hyperideal.NativeRadicand.radicand_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0}
    _root_.Reg.D5.S3.Geometry.Hyperideal.NativeRadicand.signature
    (fun _ p z => rad p.1 p.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
    definition := none
    coordinates := #[0,1]
    readouts := #[{ path := #["body","body","body","body","body","body","arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration_2
end
end Reg.D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
