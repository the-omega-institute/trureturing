import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen
import Reg.Support.DependentFamily

/-! Both sides of each original real inequality are retained as observations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen

namespace Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

namespace Core

def actual : Realization signature :=
  realize signature (fun role κ y => if role then
    ((y ^ (2 : ℝ) + y + 1) ^ κ - (y + 1) ^ κ) ^ (2 : ℝ) else
    ((y ^ (2 : ℝ) + 2) ^ κ - 2 ^ κ) * ((y + 1) ^ κ - 1) ^ (2 : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def intervention (i : Bool) : Realization signature :=
  realize signature (fun role κ y => if role = i then actual.readout (!i) κ y
    else actual.readout role κ y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ y : ℝ}, 1 < κ → 1 < y → R.readout false κ y > R.readout true κ y

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (κ := 2) (y := 2) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hb

private theorem intervention_law (i : Bool) : ¬ arena.Law (intervention i) := by
  intro h
  have hb := h (κ := 2) (y := 2) (by norm_num) (by norm_num)
  cases i <;> exact (lt_irrefl _) hb

def family : Registration arena (type_of% @lemma415_core) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lemma415_core, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervention i, ?_, rfl, intervention_law i⟩
      intro j hji
      funext κ y
      simp only [intervention, realize, ite_eq_right hji]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    cases i <;> norm_num [actual, realize, Real.rpow_ofNat]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lemma415_core) (Realization signature) Type Unit where
  unitName := `LcmPowerLemmaFifteen.lemma415_core.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen.Core.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun role κ y => if role then
    ((y ^ (2 : ℝ) + y + 1) ^ κ - (y + 1) ^ κ) ^ (2 : ℝ) else
    ((y ^ (2 : ℝ) + 2) ^ κ - 2 ^ κ) * ((y + 1) ^ κ - 1) ^ (2 : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Core

namespace FunctionComparison

def actual : Realization signature :=
  realize signature (fun role κ y => if role then lcmPowerF κ (y ^ (2 : ℝ) / 2) 1
    else lcmPowerF κ y 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def intervention (i : Bool) : Realization signature :=
  realize signature (fun role κ y => if role = i then actual.readout (!i) κ y
    else actual.readout role κ y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ y : ℝ}, 1 < κ → Real.sqrt 2 < y → R.readout false κ y < R.readout true κ y

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (κ := 2) (y := 3) (by norm_num) (by
    exact (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num))
  norm_num [rejected, realize] at hb

private theorem intervention_law (i : Bool) : ¬ arena.Law (intervention i) := by
  intro h
  have hb := h (κ := 2) (y := 3) (by norm_num) (by
    exact (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num))
  cases i <;> exact (lt_irrefl _) hb

private theorem left_pos : 0 < lcmPowerF 2 3 2 := by
  norm_num [lcmPowerF, Real.rpow_ofNat]
  exact div_pos (Real.log_pos (by norm_num)) (by positivity)

private theorem right_pos : 0 < lcmPowerF 2 ((3 : ℝ) ^ (2 : ℝ) / 2) 1 := by
  norm_num [lcmPowerF, Real.rpow_ofNat]
  exact div_pos (Real.log_pos (by norm_num)) (by positivity)

def family : Registration arena (type_of% @lemma415_F) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lemma415_F, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervention i, ?_, rfl, intervention_law i⟩
      intro j hji
      funext κ y
      simp only [intervention, realize, ite_eq_right hji]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨2, 0, 3, ?_⟩
    cases i
    · change lcmPowerF 2 0 2 ≠ lcmPowerF 2 3 2
      have hz : lcmPowerF 2 0 2 = 0 := by simp [lcmPowerF]
      rw [hz]
      exact left_pos.ne
    · change lcmPowerF 2 ((0 : ℝ) ^ (2 : ℝ) / 2) 1 ≠ lcmPowerF 2 ((3 : ℝ) ^ (2 : ℝ) / 2) 1
      have hz : lcmPowerF 2 ((0 : ℝ) ^ (2 : ℝ) / 2) 1 = 0 := by simp [lcmPowerF]
      rw [hz]
      exact right_pos.ne

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lemma415_F) (Realization signature) Type Unit where
  unitName := `LcmPowerLemmaFifteen.lemma415_F.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen.FunctionComparison.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun role κ y => if role then lcmPowerF κ (y ^ (2 : ℝ) / 2) 1
    else lcmPowerF κ y 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FunctionComparison
namespace FullLemma

abbrev fullSignature : Signature where
  Params := ℝ
  State _ := ℝ × ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ × ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization fullSignature :=
  realize fullSignature (fun role κ p => if role then
    (Real.sqrt (2 * p.1), lcmPowerF κ p.1 1) else
    (p.2, lcmPowerF κ p.2 2)) (fun e => nomatch e)

def rejected : Realization fullSignature :=
  realize fullSignature (fun _ _ _ => (0, 0)) (fun e => nomatch e)

def intervention (i : Bool) : Realization fullSignature :=
  realize fullSignature (fun role κ p => if role = i then actual.readout (!i) κ p
    else actual.readout role κ p) (fun e => nomatch e)

abbrev arena : Arena where
  signature := fullSignature
  Law R := ∀ {κ x x' : ℝ}, 1 < κ → 1 < x → 1 < x' →
    (R.readout false κ (x, x')).2 = (R.readout true κ (x, x')).2 →
      (R.readout false κ (x, x')).1 < (R.readout true κ (x, x')).1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (κ := 2) (x := 2) (x' := 2) (by norm_num) (by norm_num)
    (by norm_num) rfl
  exact (lt_irrefl (0 : ℝ)) hb

private theorem intervention_law (i : Bool) : ¬ arena.Law (intervention i) := by
  intro h
  cases i
  · have hb := h (κ := 2) (x := 2) (x' := 2) (by norm_num) (by norm_num)
      (by norm_num) rfl
    exact (lt_irrefl _) hb
  · have hb := h (κ := 2) (x := 2) (x' := 2) (by norm_num) (by norm_num)
      (by norm_num) rfl
    exact (lt_irrefl _) hb

def family : Registration arena (type_of% @lemma415) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lemma415, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervention i, ?_, rfl, intervention_law i⟩
      intro j hji
      funext κ p
      simp only [intervention, realize, ite_eq_right hji]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨2, (0, 0), (2, 2), ?_⟩
    intro he
    have hh := congrArg Prod.fst he
    cases i <;> norm_num [actual, realize] at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lemma415) (Realization fullSignature) Type Unit where
  unitName := `LcmPowerLemmaFifteen.lemma415.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen.FullLemma.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fullSignature (fun role κ p => if role then
    (Real.sqrt (2 * p.1), lcmPowerF κ p.1 1) else
    (p.2, lcmPowerF κ p.2 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ × ℝ)
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FullLemma
end Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen
