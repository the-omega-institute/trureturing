import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Matrix.HwangKimTwoDimensionalCriterion

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix.HwangKimTwoDimensionalCriterion
open _root_.D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation
open LeanInformationAudit Matrix
open scoped MatrixOrder ComplexOrder

namespace Reg.D5.S3.Quantum.Matrix.HwangKimTwoDimensionalCriterion
noncomputable section
open Classical

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Mat (fun _ => Mat) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ L W => decide (NearOrder L W)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {L W : Mat}, L.PosDef → W.PosDef → L.det = 1 →
    (R.readout () L W = true ↔
      1 ≤ Real.sqrt W.det.re ∧
      (W.trace.re + Real.sqrt W.det.re * L.trace.re)^2 -
        (1 + Real.sqrt W.det.re)^2 *
          ((L*W).trace.re + 2 * Real.sqrt W.det.re) ≤ 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law (L := 1) (W := 1) Matrix.PosDef.one Matrix.PosDef.one (by simp)
  norm_num [rejected, realize, Matrix.trace_one] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let W : Mat := (1/4 : ℝ) • 1
  have hW : W.PosDef := Matrix.PosDef.one.smul (by norm_num)
  have hyes : NearOrder (1 : Mat) 1 := by
    rw [near_order_iff Matrix.PosDef.one Matrix.PosDef.one (by simp)]
    norm_num [Matrix.trace_one]
  have hno : ¬ NearOrder (1 : Mat) W := by
    rw [near_order_iff Matrix.PosDef.one hW (by simp)]
    norm_num [W, Matrix.det_fin_two, Matrix.one_apply]
  refine ⟨1, 1, W, ?_⟩
  change decide (NearOrder (1 : Mat) 1) ≠ decide (NearOrder (1 : Mat) W)
  simp [hyes, hno]

def evidence : Registration arena (type_of% (@near_order_iff)) where
  actual := actual
  bridge := by
    simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by
    intro L W hL hW hd
    simpa only [actual, realize, decide_eq_true_eq] using near_order_iff hL hW hd,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Matrix.HwangKimTwoDimensionalCriterion.near_order_iff)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.HwangKimTwoDimensionalCriterion.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HwangKimTwoDimensionalCriterion.evidence
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
    owner := `D5.S3.Quantum.Matrix.HwangKimTwoDimensionalCriterion
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.Quantum.Matrix.HwangKimTwoDimensionalCriterion

/- Unfinished registration audit, tracked with the complete source return:
https://github.com/the-omega-institute/trureturing/issues/29594
The faithful source-equivalence, actual law, rejected-law variation,
whole-family sensitivity and observational dependence all compile.
The current inspector reports declared_unresolved, IE-C050 ClosedTruthReadout,
unclassified_form / source.unlinked_operand, Classical.choice;
source_operand=Classical.choice. This is not declared_validated and does not
waive kernel, sorry, axiom, source fidelity, freeze or other required checks.
-/
