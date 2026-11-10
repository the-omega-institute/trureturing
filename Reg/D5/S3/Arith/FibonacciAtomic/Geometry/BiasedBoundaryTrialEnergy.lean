import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrialEnergy
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Original stopping-cylinder extension with its actual squared edge-norm readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrialEnergy

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrialEnergy
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy (H Edge)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace (M J cylinder b)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection (atomMean)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping (Threshold A Vt)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm (D energy)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory
open scoped BigOperators ENNReal

abbrev signature : Signature where
  Params := Unit
  State _ := H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖ ^ 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t : Threshold) (F : Vt t), ∃ z : H,
    z = ∑ p ∈ A t, lp.single 2 p (atomMean p F.val) ∧
    J z = F.val ∧
    R.readout () () z = ∑ p ∈ A t, (atomMean p F.val) ^ 2 ∧
    F.val ∈ D ∧
    ‖F.val‖ ^ 2 = ∑ p ∈ A t,
      M.real (cylinder p.val) * (atomMean p F.val) ^ 2 ∧
    energy F.val ≤ ‖z‖ ^ 2 ∧
    (F.val ≠ 0 →
      b * t.val * ‖z‖ ^ 2 < ‖F.val‖ ^ 2 ∧
      ‖z‖ ^ 2 < (b * t.val)⁻¹ * ‖F.val‖ ^ 2 ∧
      energy F.val < (b * t.val)⁻¹ * ‖F.val‖ ^ 2)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let t : Threshold := ⟨1/2,by norm_num,by norm_num⟩
  obtain ⟨z,_,_,he,_⟩ := h t 0
  change (-1 : ℝ) = _ at he
  simp at he

def familyRegistration : Registration arena (type_of% actual_stopping_trial_energy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_stopping_trial_energy,rejected,rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected,?_,rfl,rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    let p : Edge := ⟨[false],by simp⟩
    refine ⟨(),(0 : H),lp.single 2 p (1 : ℝ),?_⟩
    change ‖(0 : H)‖ ^ 2 ≠ ‖(lp.single 2 p (1 : ℝ) : H)‖ ^ 2
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_stopping_trial_energy)
    (type_of% (realize signature (fun _ _ z => ‖z‖ ^ 2) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrialEnergy.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrialEnergy.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => ‖z‖ ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrialEnergy,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body","body","arg","body","arg","arg","fn","arg","fn","arg"],
      stateBinder := 2, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrialEnergy
