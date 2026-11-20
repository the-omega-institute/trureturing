import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive
import Reg.Support.SingleDependentReadout

/-! The complete unbounded source law with the witness as the selected observation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open LeanInformationAudit Real Finset
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
open _root_.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive

namespace Reg.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ B : ℕ, ∃ n : ℕ,
    B < R.readout () () n ∧ 0 < n ∧ PrimitiveNonDeficient n ∧ KLPrimitive n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, hn, hpos, hdef, hprimitive⟩ := h 0
  change 0 < 0 at hn
  exact (Nat.lt_irrefl 0) hn

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive.result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive.result,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    exact Nat.zero_ne_one

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive.result)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive.result.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace RoughLower

attribute [local instance] Classical.propDecidable

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Finset ℕ), (∀ p ∈ M, p.Prime) →
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (X : ℝ) ^ (79 / 80 : ℝ) ≤ R.readout () ()
        (((Finset.Icc 1 X).filter fun n =>
          Odd n ∧ Squarefree n ∧ PrimitiveNonDeficient n ∧ ∀ p ∈ M, ¬ p ∣ n).card)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨X₀, hX₀⟩ := h ∅ (by simp)
  have hx := hX₀ (max X₀ 1) (le_max_left _ _)
  change ((max X₀ 1 : ℕ) : ℝ) ^ (79 / 80 : ℝ) ≤ 0 at hx
  have hp : (0 : ℝ) < (max X₀ 1 : ℕ) := by
    exact_mod_cast (show 0 < max X₀ 1 by omega)
  exact (Real.rpow_pos_of_pos hp _).not_ge hx

def family : Registration arena
    (type_of% @rough_primitive_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@rough_primitive_lower_bound,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rough_primitive_lower_bound)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive.rough_primitive_lower_bound.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive.RoughLower.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RoughLower

end Reg.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive
