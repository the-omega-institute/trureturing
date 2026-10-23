import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.LogLogHigherDerivative
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.LogLogHigherDerivative

open _root_.D5.S3.Arith.Robin.LogLogHigherDerivative
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- The outer logarithm is varied; its inner logarithm and the open domain stay fixed. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, ∀ {x : ℝ}, 1 < x →
    0 < (-1 : ℝ) ^ m *
      iteratedDeriv (m + 1) (fun y : ℝ => R.readout () () (Real.log y)) x

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0 (x := 2) (by norm_num)
  norm_num [rejected, realize, iteratedDeriv_const] at hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (by norm_num)).ne

def family : Registration arena (type_of% signed_iteratedDeriv_logLog_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨signed_iteratedDeriv_logLog_pos, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    signed_iteratedDeriv_logLog_pos
    (type_of% (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)))
    Unit Unit where
  unitName := `D5.S3.Arith.Robin.LogLogHigherDerivative.signed_iteratedDeriv_logLog_pos.audit
  realizationName := `Reg.D5.S3.Arith.Robin.LogLogHigherDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.LogLogHigherDerivative
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "fn", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

abbrev kernelSignature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev kernelArena : Arena where
  signature := kernelSignature
  Law R := ∀ m a b : ℕ, ∀ {x : ℝ}, 1 < x →
    0 < R.readout () ⟨m, a, b⟩ x

def kernelActual : Realization kernelSignature :=
  realize kernelSignature (fun _ p x => positiveKernel p.1 p.2.1 p.2.2 x)
    (fun e => nomatch e)

def kernelRejected : Realization kernelSignature :=
  realize kernelSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem kernel_rejected_law : ¬ kernelArena.Law kernelRejected := by
  intro h
  have hbad := h 0 0 0 (x := 2) (by norm_num)
  norm_num [kernelRejected, realize] at hbad

def kernelFamily : Registration kernelArena (type_of% (@positiveKernel_pos)) where
  actual := kernelActual
  bridge := Iff.rfl
  variation := ⟨@positiveKernel_pos, kernelRejected, kernel_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨kernelRejected, ?_, rfl, kernel_rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _i
    refine ⟨⟨0, 0, 0⟩, 1, 2, ?_⟩
    change positiveKernel 0 0 0 1 ≠ positiveKernel 0 0 0 2
    have hp := positiveKernel_pos 0 0 0 (by norm_num : (1 : ℝ) < 2)
    have hz : positiveKernel 0 0 0 1 = 0 := by norm_num [positiveKernel]
    rw [hz]
    exact hp.ne

def kernelAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positiveKernel_pos)
    (type_of% (realize kernelSignature (fun _ p x => positiveKernel p.1 p.2.1 p.2.2 x) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.LogLogHigherDerivative.positiveKernel_pos.audit
  realizationName := `Reg.D5.S3.Arith.Robin.LogLogHigherDerivative.kernelFamily
  realizationSource := none
  generated := false
  arena := .source ⟨kernelArena⟩
  objectArena := .source ⟨kernelArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source kernelArena ⟨kernelFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize kernelSignature (fun _ p x => positiveKernel p.1 p.2.1 p.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.LogLogHigherDerivative
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms kernelFamily

end Reg.D5.S3.Arith.Robin.LogLogHigherDerivative
