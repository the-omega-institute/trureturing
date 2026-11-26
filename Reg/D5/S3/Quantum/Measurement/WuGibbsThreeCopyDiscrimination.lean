import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the state trace, payoff bounds and transpose identities. -/

namespace Reg.D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite (partialTranspose)
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace States

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Mat) (fun _ => ℂ)

private def actual : Realization signature :=
  realize signature (fun _ _ M => M.trace) (fun e => nomatch e)

private def erasedTrace : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x z : ℝ) (_ : x ^ 2 + z ^ 2 < 1),
    (threeCopy x z).PosDef ∧ R.readout () () (threeCopy x z) = 1 ∧
      (threeCopy (-x) z).PosDef ∧ (threeCopy (-x) z).trace = 1

private theorem rejected_law : ¬ arena.Law erasedTrace := by
  intro h
  exact zero_ne_one ((h 0 0 (by norm_num)).2.1 : (0 : ℂ) = 1)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), threeCopy 0 0, 0, ?_⟩
  change (threeCopy 0 0).trace ≠ (0 : Mat).trace
  simp [(threeCopy_states 0 0 (by norm_num)).2.1]

def family : Registration arena (type_of% @threeCopy_states) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨threeCopy_states, erasedTrace, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erasedTrace rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@threeCopy_states) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination.threeCopy_states.audit
  realizationName := `Reg.D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination.States.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M.trace) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end States

private abbrev comparison : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def weakBound : Realization comparison :=
  realize comparison (fun _ _ payoff bound => payoff ≤ bound) (fun e => nomatch e)

private def strictBound : Realization comparison :=
  realize comparison (fun _ _ payoff bound => payoff < bound) (fun e => nomatch e)

private def reverseBound : Realization comparison :=
  realize comparison (fun _ _ payoff bound => bound ≤ payoff) (fun e => nomatch e)

private theorem weak_dependence : ObservationalDependence comparison weakBound := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  change (fun bound : ℝ => 0 ≤ bound) = (fun bound : ℝ => 1 ≤ bound) at h
  exact (not_le_of_gt zero_lt_one) ((congrFun h 0).mp le_rfl)

private theorem strict_dependence : ObservationalDependence comparison strictBound := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  change (fun bound : ℝ => 0 < bound) = (fun bound : ℝ => 1 < bound) at h
  exact lt_irrefl 1 ((congrFun h 1).mp zero_lt_one)

namespace Helstrom

private abbrev arena : Arena where
  signature := comparison
  Law R := ∀ (x z : ℝ) (_ : 0 < x) (_ : x ^ 2 + z ^ 2 < 1),
    let D := difference x z
    let P := optimalEffect z
    P.PosSemidef ∧ (1 - P).PosSemidef ∧ (P * D).trace.re = bias x z ∧
      traceNorm D = 2 * bias x z ∧
      ∀ F : Mat, F.PosSemidef → (1 - F).PosSemidef →
        R.readout () () (F * D).trace.re (bias x z) ∧
          ((F * D).trace.re = bias x z ↔ F = P)

private theorem rejected_law : ¬ arena.Law strictBound := by
  intro h
  have hx : (0 : ℝ) < 1 / 2 := by norm_num
  have hi : (1 / 2 : ℝ) ^ 2 + 0 ^ 2 < 1 := by norm_num
  obtain ⟨hp, hpc, hval, _, _⟩ := threeCopy_helstrom (1 / 2) 0 hx hi
  have hstrict : (optimalEffect 0 * difference (1 / 2) 0).trace.re < bias (1 / 2) 0 :=
    ((h (1 / 2) 0 hx hi).2.2.2.2 (optimalEffect 0) hp hpc).1
  exact (ne_of_lt hstrict) hval

def family : Registration arena (type_of% @threeCopy_helstrom) where
  actual := weakBound
  bridge := Iff.rfl
  variation := ⟨threeCopy_helstrom, strictBound, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law weakBound strictBound rejected_law
  dependence := weak_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@threeCopy_helstrom) (Realization comparison) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination.threeCopy_helstrom.audit
  realizationName := `Reg.D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination.Helstrom.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize comparison (fun _ _ payoff bound => payoff ≤ bound) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg",
        "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Helstrom

namespace DifferenceTranspose

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Mat) (fun _ => Mat → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ A B => A = B) (fun e => nomatch e)

private def unequal : Realization signature :=
  realize signature (fun _ _ A B => A ≠ B) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ x z : ℝ, R.readout () () (firstTranspose (difference x z)) (difference x z)

private theorem rejected_law : ¬ arena.Law unequal := by
  intro h
  exact h 0 0 (difference_firstTranspose 0 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  change (fun B : Mat => 0 = B) = (fun B : Mat => 1 = B) at h
  exact one_ne_zero ((congrFun h 0).mp (rfl : (0 : Mat) = 0))

def family : Registration arena (type_of% @difference_firstTranspose) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨difference_firstTranspose, unequal, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual unequal rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@difference_firstTranspose) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination.difference_firstTranspose.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination.DifferenceTranspose.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A B => A = B) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DifferenceTranspose

namespace SignEntry

private def actual : Realization comparison :=
  realize comparison (fun _ _ left right => left = right) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := comparison
  Law R := ∀ z : ℝ,
    R.readout () () (sign z (0,0,0) (1,1,1) - sign z (1,0,0) (0,1,1)).re
      (2 / 3 * (1 - (1 - z ^ 2) / Real.sqrt (1 + z ^ 2 + z ^ 4)))

private theorem rejected_law : ¬ arena.Law strictBound := by
  intro h
  exact (ne_of_lt (h 0)) (sign_firstTranspose_entry 0)

private theorem dependence : ObservationalDependence comparison actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  change (fun right : ℝ => 0 = right) = (fun right : ℝ => 1 = right) at h
  exact one_ne_zero ((congrFun h 0).mp (rfl : (0 : ℝ) = 0))

def family : Registration arena (type_of% @sign_firstTranspose_entry) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sign_firstTranspose_entry, strictBound, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual strictBound rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sign_firstTranspose_entry) (Realization comparison) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination.sign_firstTranspose_entry.audit
  realizationName := `Reg.D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination.SignEntry.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize comparison (fun _ _ left right => left = right) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SignEntry

namespace Ppt

private abbrev arena : Arena where
  signature := comparison
  Law R := ∀ (x z : ℝ) (_ : 0 < x) (_ : 0 < z) (_ : x ^ 2 + z ^ 2 < 1)
    (F : Mat) (_ : F.PosSemidef) (_ : (1 - F).PosSemidef)
    (_ : (firstTranspose F).PosSemidef) (_ : (1 - firstTranspose F).PosSemidef),
    R.readout () () (F * difference x z).trace.re (bias x z)

private theorem rejected_law : ¬ arena.Law reverseBound := by
  intro h
  have hx : (0 : ℝ) < 1 / 2 := by norm_num
  have hi : (1 / 2 : ℝ) ^ 2 + (1 / 2 : ℝ) ^ 2 < 1 := by norm_num
  have h0 : (0 : Mat).PosSemidef := Matrix.PosSemidef.zero
  have h1 : (1 - (0 : Mat)).PosSemidef := by
    simpa using (Matrix.PosSemidef.one : (1 : Mat).PosSemidef)
  have hΓ : firstTranspose (0 : Mat) = 0 := by
    ext i j
    simp [firstTranspose, partialTranspose]
  have hΓ0 : (firstTranspose (0 : Mat)).PosSemidef := hΓ.symm ▸ h0
  have hΓ1 : (1 - firstTranspose (0 : Mat)).PosSemidef := hΓ.symm ▸ h1
  have hlt := threeCopy_ppt_lt (1 / 2) (1 / 2) hx hx hi 0 h0 h1 hΓ0 hΓ1
  exact (not_lt_of_ge (h (1 / 2) (1 / 2) hx hx hi 0 h0 h1 hΓ0 hΓ1)) hlt

def family : Registration arena (type_of% @threeCopy_ppt_lt) where
  actual := strictBound
  bridge := Iff.rfl
  variation := ⟨threeCopy_ppt_lt, reverseBound, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law strictBound reverseBound rejected_law
  dependence := strict_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@threeCopy_ppt_lt) (Realization comparison) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination.threeCopy_ppt_lt.audit
  realizationName := `Reg.D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination.Ppt.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize comparison (fun _ _ payoff bound => payoff < bound) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Ppt

end
end Reg.D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination
