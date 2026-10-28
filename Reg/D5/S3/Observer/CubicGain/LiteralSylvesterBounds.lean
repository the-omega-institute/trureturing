import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.LiteralSylvesterBounds
import Reg.Support.SingleDependentReadout
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.LiteralSylvesterBounds
open Polynomial
open _root_.D5.S3.Observer.CubicGain.ActualMinorLift
open _root_.D5.S3.Observer.CubicGain.LiteralSylvesterBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Polynomial ℤ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ p => p.natDegree) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 286) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, X, by simp [actual, realize]⟩

namespace resultant_bound
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : Fin 2, R.readout () () (actualResultant k) ≤ 285
private theorem rejected_law : ¬ arena.Law rejected := by
  simp [arena, rejected, realize]
private theorem actual_law : arena.Law actual := by
  simpa [arena, actual, realize] using @literal_resultant_degree_bound
def source_registration : Registration arena (type_of% @literal_resultant_degree_bound) where
  actual := actual
  bridge := by simp only [arena, actual, realize]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@literal_resultant_degree_bound) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.LiteralSylvesterBounds.literal_resultant_degree_bound.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.LiteralSylvesterBounds.resultant_bound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p.natDegree) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.LiteralSylvesterBounds
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body","fn","arg","fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end resultant_bound

namespace minor_bound
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () actualMinorA0 ≤ 252 ∧ R.readout () () actualMinorC0 ≤ 253
private theorem rejected_law : ¬ arena.Law rejected := by
  simp [arena, rejected, realize]
private theorem actual_law : arena.Law actual := by
  simpa [arena, actual, realize] using @literal_minor_degree_bounds
def source_registration : Registration arena (type_of% @literal_minor_degree_bounds) where
  actual := actual
  bridge := by simp only [arena, actual, realize]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@literal_minor_degree_bounds) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.LiteralSylvesterBounds.literal_minor_degree_bounds.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.LiteralSylvesterBounds.minor_bound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p.natDegree) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.LiteralSylvesterBounds
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["fn","arg","fn","arg","fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false },
      { path := #["arg","fn","arg","fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end minor_bound

namespace exact_degrees
abbrev arena : Arena where
  signature := signature
  Law R := (∀ k : Fin 2, R.readout () () (actualResultant k) = 285) ∧ R.readout () () actualMinorA0 = 252 ∧ R.readout () () actualMinorC0 = 253
private theorem rejected_law : ¬ arena.Law rejected := by
  simp [arena, rejected, realize]
private theorem actual_law : arena.Law actual := by
  simpa [arena, actual, realize] using @literal_elimination_exact_degrees
def source_registration : Registration arena (type_of% @literal_elimination_exact_degrees) where
  actual := actual
  bridge := by simp only [arena, actual, realize]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@literal_elimination_exact_degrees) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.LiteralSylvesterBounds.literal_elimination_exact_degrees.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.LiteralSylvesterBounds.exact_degrees.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p.natDegree) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.LiteralSylvesterBounds
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["fn","arg","body","fn","arg","fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false },
      { path := #["arg","fn","arg","fn","arg","fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false },
      { path := #["arg","arg","fn","arg","fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end exact_degrees

namespace source_elimination
open _root_.D5.S3.Observer.CubicGain.SelectedRootCommonZero
open _root_.D5.S3.Observer.CubicGain.LiteralElimination
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 2) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ k b => (actualResultant k).eval₂ (Int.castRingHom ℝ) b)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ t b : ℝ,
    sourceBt 0 t b * sourceBb 1 t b - sourceBb 0 t b * sourceBt 1 t b = 0 →
    sourceBt 0 t b * sourceBb 2 t b - sourceBb 0 t b * sourceBt 2 t b = 0 →
    sourceBt 1 t b * sourceBb 2 t b - sourceBb 1 t b * sourceBt 2 t b = 0 →
    sourceD t b = 0 ∨ ((∀ k : Fin 2, R.readout () k b = 0) ∧
      (t * b) * evalB b actualMinorA0 + evalB b actualMinorC0 = 0)
private theorem center_e0 : (sourceE0 (1/8 : ℝ)).eval (9/16) = 0 := by
  norm_num [sourceE0]
private theorem center_e1 : (sourceE1 (1/8 : ℝ)).eval (9/16) = 0 := by
  norm_num [sourceE1]
private theorem center_e2 : (sourceE2 (1/8 : ℝ)).eval (9/16) = 0 := by
  norm_num [sourceE2]
private theorem center_d : sourceD (9/2 : ℝ) (1/8) ≠ 0 := by
  norm_num [sourceD, sourceJ, sourceN]
private theorem center_minors :
    (sourceBt 0 (9/2) (1/8) * sourceBb 1 (9/2) (1/8) -
      sourceBb 0 (9/2) (1/8) * sourceBt 1 (9/2) (1/8) = 0) ∧
    (sourceBt 0 (9/2) (1/8) * sourceBb 2 (9/2) (1/8) -
      sourceBb 0 (9/2) (1/8) * sourceBt 2 (9/2) (1/8) = 0) ∧
    (sourceBt 1 (9/2) (1/8) * sourceBb 2 (9/2) (1/8) -
      sourceBb 1 (9/2) (1/8) * sourceBt 2 (9/2) (1/8) = 0) := by
  have hb : (1 / 2097152 : ℝ) ≠ 0 := by norm_num
  have h0 := source_e0_normalization (9/2) (1/8)
  have h1 := source_e1_normalization (9/2) (1/8)
  have h2 := source_e2_normalization (9/2) (1/8)
  norm_num only [show (9/2 : ℝ)*(1/8) = 9/16 by norm_num,
    center_e0, center_e1, center_e2, mul_zero] at h0 h1 h2
  exact ⟨(mul_eq_zero.mp h0.symm).resolve_left hb,
    (mul_eq_zero.mp h1.symm).resolve_left hb,
    (mul_eq_zero.mp h2.symm).resolve_left hb⟩
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := h (9/2) (1/8) center_minors.1 center_minors.2.1 center_minors.2.2
  rcases hc with hd | ⟨hr, _⟩
  · exact center_d hd
  · have hz := hr 0
    norm_num [rejected, realize] at hz
private theorem dependence : ObservationalDependence signature actual := by
  let p := (actualResultant 0).map (Int.castRingHom ℝ)
  have hd : p.natDegree = 285 := by
    rw [show p = (actualResultant 0).map (Int.castRingHom ℝ) from rfl,
      natDegree_map_eq_of_injective (Int.cast_injective (α := ℝ))]
    exact literal_elimination_exact_degrees.1 0
  have he : ∃ b : ℝ, p.eval b ≠ p.eval 0 := by
    by_contra hn
    push_neg at hn
    have hp : p = C (p.eval 0) := Polynomial.funext (by simpa using hn)
    rw [hp, natDegree_C] at hd
    norm_num at hd
  obtain ⟨b, hb⟩ := he
  intro i
  refine ⟨0, b, 0, ?_⟩
  simpa only [actual, realize, p, eval_map] using hb
private theorem actual_law : arena.Law actual := source_critical_literal_elimination
def source_registration : Registration arena (type_of% @source_critical_literal_elimination) where
  actual := actual
  bridge := by simp only [arena, actual, realize]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@source_critical_literal_elimination) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.LiteralSylvesterBounds.source_critical_literal_elimination.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.LiteralSylvesterBounds.source_elimination.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ k b => (actualResultant k).eval₂ (Int.castRingHom ℝ) b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.LiteralSylvesterBounds
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body","body","body","body","body","arg","fn","arg","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end source_elimination
end Reg.D5.S3.Observer.CubicGain.LiteralSylvesterBounds
