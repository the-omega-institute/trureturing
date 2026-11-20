import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture11
import Reg.Support.SingleDependentReadout

/-! The real inequality in the primitive exceptional-set counting estimate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real Filter LeanInformationAudit
open scoped Topology
open _root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture11
open _root_.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive
  (rough_primitive_lower_bound)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive (PrimitiveNonDeficient)
open _root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity (radicalComponentSet count)

namespace Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture11

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
    (type_of% @exceptional_bound) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@exceptional_bound,
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
    (@exceptional_bound)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture11.exceptional_bound.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture11.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture11
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

namespace R

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => Filter ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 𝓝 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (S : Set ℕ), (∀ n ∈ S, PrimitiveNonDeficient n) →
    (∀ᶠ X : ℕ in atTop,
      (X : ℝ) ^ (79 / 80 : ℝ) ≤ (count S X : ℝ)) →
    Tendsto (fun X : ℕ =>
      (count (radicalComponentSet 2 ∩ S) X : ℝ) / count S X)
      atTop (R.readout () () 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let S : Set ℕ := {n | Odd n ∧ Squarefree n ∧ PrimitiveNonDeficient n ∧
    ∀ p ∈ (∅ : Finset ℕ), ¬ p ∣ n}
  have hS : ∀ n ∈ S, PrimitiveNonDeficient n := fun _ hn => hn.2.2.1
  obtain ⟨X₀, hX₀⟩ := rough_primitive_lower_bound ∅ (by simp)
  have hlow : ∀ᶠ X : ℕ in atTop,
      (X : ℝ) ^ (79 / 80 : ℝ) ≤ (count S X : ℝ) := by
    filter_upwards [eventually_ge_atTop X₀] with X hX
    simpa only [count, S, Set.mem_setOf_eq] using hX₀ X hX
  have bad := h S hS hlow
  exact Filter.atTop_neBot.ne (Filter.tendsto_bot_right_iff.mp bad)

def family : Registration arena
    (type_of% @relative_density_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@relative_density_one, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    change 𝓝 (0 : ℝ) ≠ 𝓝 1
    exact nhds_injective.ne zero_ne_one

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@relative_density_one)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture11.relativeAudit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture11.R.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture11
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end R

end Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture11
