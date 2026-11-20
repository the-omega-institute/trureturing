import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.ZelinskyPrimitiveExceptionalSet
import Reg.Support.SingleDependentReadout

/-! The real inequality in the primitive exceptional-set counting estimate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive (PrimitiveNonDeficient)
open _root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity (radicalComponentSet)

namespace Reg.D5.S3.Arith.Abundancy.ZelinskyPrimitiveExceptionalSet

attribute [local instance] Classical.propDecidable

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ K : ℝ, 0 < K ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    R.readout () ()
      (((Icc 1 X).filter fun n =>
        PrimitiveNonDeficient n ∧ n ∉ radicalComponentSet 2).card : ℝ)
      (K * (X : ℝ) ^ (39 / 40 : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨K, hK, X₀, hX⟩
  exact hX X₀ le_rfl

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyPrimitiveExceptionalSet.result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyPrimitiveExceptionalSet.result,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh := congrFun he (0 : ℝ)
    change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at hh
    have hbad : (1 : ℝ) ≤ 0 := Eq.mp hh le_rfl
    norm_num at hbad

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyPrimitiveExceptionalSet.result)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyPrimitiveExceptionalSet.result.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyPrimitiveExceptionalSet.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyPrimitiveExceptionalSet
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Abundancy.ZelinskyPrimitiveExceptionalSet
