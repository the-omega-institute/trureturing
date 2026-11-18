import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.ExceptionCount.ZetaTail
import Reg.Support.SingleDependentReadout

/-! The full parameter family of the uniform omitted Euler-product tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.ExceptionCount.ZetaTail

namespace Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.ZetaTail

namespace UniformTail

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {delta : ℝ}, 0 < delta →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ P : ℝ), 1 + delta ≤ κ → 2 ≤ P →
      R.readout () ()
        (log (riemannZeta (κ : ℂ)).re +
          ∑ p ∈ (Ioc 0 ⌊P⌋₊).filter Nat.Prime, log (1 - (p : ℝ) ^ (-κ)))
        (C * P ^ (-(delta / 2)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨C, hC, hfalse⟩ := h (delta := 1) (by norm_num)
  exact hfalse 2 2 (by norm_num) (by norm_num)

def family : Registration arena (type_of% @uniform_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@uniform_tail, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_tail) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.ExceptionCount.ZetaTail.uniform_tail.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.ZetaTail.UniformTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.ExceptionCount.ZetaTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end UniformTail

end Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.ZetaTail
