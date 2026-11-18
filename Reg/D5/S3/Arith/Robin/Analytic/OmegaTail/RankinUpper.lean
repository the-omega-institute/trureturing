import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.RankinUpper
import Reg.Support.SingleDependentReadout

/-! Dependent readout for the sharp eventual counting bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper (tailCount)
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.RankinUpper

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.RankinUpper

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (epsilon : ℝ), 0 < epsilon → ∀ᶠ P : ℝ in atTop,
    R.readout () () (tailCount 1 (exp P) : ℝ)
      (exp ((2 * π / sqrt 3 + epsilon) * (P / log P ^ (3 / 2 : ℝ))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : ∀ᶠ P : ℝ in atTop, False := h 1 zero_lt_one
  exact he.exists.choose_spec

def family : Registration arena (type_of% @sharp_upper_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sharp_upper_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sharp_upper_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.RankinUpper.sharp_upper_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.RankinUpper.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.RankinUpper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.RankinUpper
