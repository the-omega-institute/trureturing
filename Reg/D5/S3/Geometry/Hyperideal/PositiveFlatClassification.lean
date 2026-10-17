import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Hyperideal.PositiveFlatClassification
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.PositiveFlatClassification
open _root_.D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
open _root_.D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open _root_.D5.S3.Geometry.Hyperideal.FourCycleEnvelopes (cosine rad numerator)
namespace Reg.D5.S3.Geometry.Hyperideal.PositiveFlatClassification

abbrev signature : Signature where
  Params := Fin 6 → ℝ
  State _ := Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ x k => rawCos x (k.natAdd 3))
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : Fin 6 → ℝ) (_hx : ∀ q, 1 < x q),
    (Genuine x ↔ ∀ q, 0 < extendedAngle x q ∧ extendedAngle x q < Real.pi) ∧
    (Genuine x ∨ ∃! k : Fin 3, Sector x k) ∧
    (∀ k : Fin 3,
      (Sector x k ↔ R.readout () x k ≤ -1) ∧
      (Sector x k ↔ ∀ q, extendedAngle x q =
        if q = k.castAdd 3 ∨ q = k.natAdd 3 then Real.pi else 0))

private def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

private def asymmetric : Fin 6 → ℝ := ![14,2,2,14,2,2]

private theorem asymmetric_readouts :
    actual.readout () asymmetric 0 = (-2610/315 : ℝ) ∧
    actual.readout () asymmetric 1 = (450/315 : ℝ) := by
  change rawCos asymmetric 3 = _ ∧ rawCos asymmetric 4 = _
  constructor
  all_goals
    simp only [rawCos,frame,asymmetric,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue]
    unfold cosine
    norm_num [numerator,rad]
    rw [div_div,← pow_two,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 315)]
    norm_num

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx : ∀ q, 1 < asymmetric q := by
    intro q
    fin_cases q <;> norm_num [asymmetric]
  have hs : Sector asymmetric 0 := by
    apply ((positive_classification asymmetric hx).2.2 0).1.mpr
    change actual.readout () asymmetric 0 ≤ -1
    rw [asymmetric_readouts.1]
    norm_num
  have hh := ((h asymmetric hx).2.2 0).1.mp hs
  norm_num [rejected,realize] at hh

/-- Complete dependent-family obligations for the original six-coordinate classifier.
Source selector and raw binding certification are separate interface obligations. -/
def classifier_family : Registration arena
    (type_of% (@_root_.D5.S3.Geometry.Hyperideal.PositiveFlatClassification.positive_classification)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Geometry.Hyperideal.PositiveFlatClassification.positive_classification,
    rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨asymmetric,0,1,?_⟩
    cases i
    rw [asymmetric_readouts.1,asymmetric_readouts.2]
    norm_num

#print axioms classifier_family

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.Hyperideal.PositiveFlatClassification.positive_classification)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ x k => rawCos x (k.natAdd 3)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Hyperideal.PositiveFlatClassification.positive_classification.opposite_raw_unit
  realizationName := `Reg.D5.S3.Geometry.Hyperideal.PositiveFlatClassification.classifier_family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨classifier_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ x k => rawCos x (k.natAdd 3)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Hyperideal.PositiveFlatClassification
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body","body","arg","arg","body","fn","arg","arg","fn","arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

namespace Budget

abbrev signature : Signature where
  Params := Σ _r : ℝ, Σ _a : ℝ, Σ _b : ℝ, Σ _c : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ x o => cosine x.1 x.2.1 x.2.2.1 o x.2.2.2.1 x.2.2.2.2)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r a b o c d : ℝ) (_hr : 1 < r) (_ha : 1 < a) (_hb : 1 < b)
      (_ho : 1 < o) (_hc : 1 < c) (_hd : 1 < d)
      (_hflat : R.readout () ⟨r,a,b,c,d⟩ o ≤ -1),
    Real.log 16+2*Real.log (r/(r-1))+2*Real.log (o/(o-1)) ≤
      2*Real.log r+2*Real.log o-Real.log a-Real.log b-Real.log c-Real.log d ∧
    Real.log 16 < Real.log 16+2*Real.log (r/(r-1))+2*Real.log (o/(o-1))

private def rejected : Realization signature := realize signature (fun _ _ _ => -1)
  (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 2 2 2 2 2 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rejected,realize])).1
  norm_num at hh
  have h2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have h16 := Real.log_pos (by norm_num : (1:ℝ) < 16)
  linarith

private theorem dependence_readouts :
    actual.readout () ⟨2,2,2,2,2⟩ 2 = (18/27 : ℝ) ∧
    actual.readout () ⟨2,2,2,2,2⟩ 3 = (15/27 : ℝ) := by
  constructor
  all_goals
    change cosine 2 2 2 _ 2 2 = _
    unfold cosine
    norm_num [numerator,rad]
    rw [div_div,← pow_two,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 27)]
    norm_num

def budget_family : Registration arena
    (type_of% (@_root_.D5.S3.Geometry.Hyperideal.PositiveFlatClassification.native_flat_budget)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Geometry.Hyperideal.PositiveFlatClassification.native_flat_budget,
    rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨2,2,2,2,2⟩,2,3,?_⟩
    rw [dependence_readouts.1,dependence_readouts.2]
    norm_num

#print axioms budget_family

def registration_2 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.Hyperideal.PositiveFlatClassification.native_flat_budget)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ x o => cosine x.1 x.2.1 x.2.2.1 o x.2.2.2.1 x.2.2.2.2)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Hyperideal.PositiveFlatClassification.native_flat_budget.raw_cosine_unit
  realizationName := `Reg.D5.S3.Geometry.Hyperideal.PositiveFlatClassification.Budget.budget_family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨budget_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ x o => cosine x.1 x.2.1 x.2.2.1 o x.2.2.2.1 x.2.2.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Hyperideal.PositiveFlatClassification
    definition := none
    coordinates := #[0,1,2,4,5]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","body","body","body","body","domain","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn","fn","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Budget

end Reg.D5.S3.Geometry.Hyperideal.PositiveFlatClassification
