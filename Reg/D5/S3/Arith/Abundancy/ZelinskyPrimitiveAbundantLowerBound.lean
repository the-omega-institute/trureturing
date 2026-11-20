import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound
import Reg.Support.SingleDependentReadout

/-! The positive counting readout in the primitive abundant lower bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive (PrimitiveNonDeficient)

namespace Reg.D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound

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
      (X : ℝ) ^ (39 / 40 : ℝ) ≤ R.readout () ()
        (((Finset.Icc 1 X).filter fun n =>
          Odd n ∧ Squarefree n ∧ PrimitiveNonDeficient n ∧ ∀ p ∈ M, ¬ p ∣ n).card)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨X₀, hX₀⟩ := h ∅ (by simp)
  have hx := hX₀ (max X₀ 1) (le_max_left _ _)
  change ((max X₀ 1 : ℕ) : ℝ) ^ (39 / 40 : ℝ) ≤ 0 at hx
  have hp : (0 : ℝ) < (max X₀ 1 : ℕ) := by
    exact_mod_cast (show 0 < max X₀ 1 by omega)
  exact (Real.rpow_pos_of_pos hp _).not_ge hx

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound.result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound.result,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound.result)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound.result.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound
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

end Reg.D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound
