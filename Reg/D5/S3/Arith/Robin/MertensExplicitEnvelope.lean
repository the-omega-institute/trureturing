import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.MertensExplicitEnvelope
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Robin.MertensExplicitEnvelope

open _root_.D5.S3.Arith.Robin.MertensExplicitEnvelope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Real Finset

noncomputable section

abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature
    (fun _ _ x => (∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p))⁻¹)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ _ x => exp eulerMascheroniConstant * log x *
      exp ((19 / 10 : ℝ) / log x) + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ}, 286 ≤ x →
    R.readout () () x ≤ exp eulerMascheroniConstant * log x *
      exp ((19 / 10 : ℝ) / log x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (x := 286) le_rfl
  change exp eulerMascheroniConstant * log 286 * exp ((19 / 10 : ℝ) / log 286) + 1 ≤
    exp eulerMascheroniConstant * log 286 * exp ((19 / 10 : ℝ) / log 286) at hb
  linarith

def family : Registration arena (type_of% (@prime_product_upper_effective)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_product_upper_effective, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 1, 2, ?_⟩
    change (∏ p ∈ Ioc 0 ⌊(1 : ℝ)⌋₊ with p.Prime, (1 - (1 : ℝ) / p))⁻¹ ≠
      (∏ p ∈ Ioc 0 ⌊(2 : ℝ)⌋₊ with p.Prime, (1 - (1 : ℝ) / p))⁻¹
    have h1 : (Ioc 0 1).filter Nat.Prime = ∅ := by decide
    have h2 : (Ioc 0 2).filter Nat.Prime = {2} := by decide
    norm_num only [Nat.floor_one, Nat.floor_ofNat, h1, h2,
      prod_empty, prod_singleton]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_product_upper_effective) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.MertensExplicitEnvelope.prime_product_upper_effective.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.MertensExplicitEnvelope.family
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
    owner := `D5.S3.Arith.Robin.MertensExplicitEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Arith.Robin.MertensExplicitEnvelope
