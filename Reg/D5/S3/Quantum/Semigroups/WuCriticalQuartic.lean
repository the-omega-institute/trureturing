import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCriticalQuartic

/-! Readouts of strict comparison for the quartic kernel. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCriticalQuartic

namespace Reg.D5.S3.Quantum.Semigroups.WuCriticalQuartic

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature
    (realize signature (fun _ _ x y => x < y) (fun e => nomatch e)) := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 1
  exact (lt_irrefl (1 : ℝ)) (Eq.mp he (by norm_num : (0 : ℝ) < 1))

private theorem nonzeroOnes : (1 : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have he := congrFun h 0
  norm_num at he

namespace Derivative

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {β q : ℝ}, 0 < β → 1 < q →
    ∀ (v : Fin 2 → ℝ), v ≠ 0 → R.readout () () (deriv (fun t => value β t v) q) 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (β := 1) (q := 2) (by norm_num) (by norm_num) 1 nonzeroOnes

def family : Registration arena (type_of% @deriv_value_neg) where
  actual := realize signature (fun _ _ x y => x < y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@deriv_value_neg, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law _ rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deriv_value_neg) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCriticalQuartic.deriv_value_neg.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCriticalQuartic.Derivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCriticalQuartic
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
        stateBinder := 0, functionOperand := true, stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Derivative

namespace Endpoint

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {β p r : ℝ}, 0 < β → 1 < p → p < r →
    ∀ (v : Fin 2 → ℝ), v ≠ 0 → R.readout () () 0 (value β p v - value β r v)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (β := 1) (p := 2) (r := 3) (by norm_num) (by norm_num) (by norm_num) 1 nonzeroOnes

def family : Registration arena (type_of% @endpoint_drop_pos) where
  actual := realize signature (fun _ _ x y => x < y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@endpoint_drop_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law _ rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@endpoint_drop_pos) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCriticalQuartic.endpoint_drop_pos.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCriticalQuartic.Endpoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCriticalQuartic
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
        stateBinder := 0, functionOperand := true, stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Endpoint

namespace Schur

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {β p r : ℝ}, 0 < β → 1 < p → p < r →
    R.readout () () 0 (a β p - a β r) ∧
    R.readout () () 0 (d β p - d β r - (e β p - e β r) ^ 2 / (4 * (a β p - a β r)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (β := 1) (p := 2) (r := 3) (by norm_num) (by norm_num) (by norm_num)).1

def family : Registration arena (type_of% @endpoint_schur_pos) where
  actual := realize signature (fun _ _ x y => x < y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@endpoint_schur_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law _ rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@endpoint_schur_pos) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCriticalQuartic.endpoint_schur_pos.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCriticalQuartic.Schur.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCriticalQuartic
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
        stateBinder := 0, functionOperand := true, stateOperand := none
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
        stateBinder := 0, functionOperand := true, stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Schur

end Reg.D5.S3.Quantum.Semigroups.WuCriticalQuartic
