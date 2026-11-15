import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Semigroups.ConditionedRankOneNorm
import Reg.Support.DependentFamily

open MeasureTheory Set Filter
open scoped ENNReal
open D5.S3.Quantum.Semigroups.ConditionedRankOneNorm
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Semigroups.ConditionedRankOneNorm

namespace Order
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
end Order

private theorem one_weight {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) :
    Weight ν (fun _ => 1) :=
  ⟨memLp_top_const 1, by simpa using (memLp_top_const (μ := ν) (1:ℝ)), by simp⟩

private theorem one_condition {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [NeZero ν] :
    condition ν (fun _ : Y => 1) = 1 := by
  simp [condition, lpNorm_const (p := ∞) (by simp) (NeZero.ne ν)]

namespace Envelope
abbrev signature := Order.signature
abbrev actual := Order.actual
abbrev rejected := Order.rejected

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X} [NeZero μ]
    {h g : X → ℝ} (hh : MemLp h ∞ μ) (wg : Weight μ g) {κ : ℝ}
    (hκ : 1 ≤ κ) (hk : condition μ g ≤ κ),
    ∀ᵐ x ∂μ, R.readout () () (max (h x) (lpNorm h ∞ μ / κ))
      (lpNorm (fun y => g y*h y) ∞ μ / g x)

private theorem actual_law : arena.{u}.Law actual := @envelope.{u}
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  let Y := ULift.{u} Unit
  letI : MeasurableSpace Y := ⊤
  have he := @hh Y inferInstance Measure.count inferInstance (fun _ => 1) (fun _ => 1)
    (memLp_top_const 1) (one_weight _) 1 le_rfl (by rw [one_condition])
  exact he.exists.choose_spec

def family : Registration arena.{u} (type_of% (@envelope.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    have hh : (1:ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@envelope.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Semigroups.ConditionedRankOneNorm.Envelope.unit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.ConditionedRankOneNorm.Envelope.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.ConditionedRankOneNorm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","fn","arg","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Envelope

namespace Fixed
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ x y => x+y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] [NeZero μ]
    {h g : X → ℝ} (hh : MemLp h ∞ μ) (hp : ∀ᵐ x ∂μ, 0 < h x) (wg : Weight μ g)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1),
    Sharp μ h a g (R.readout () () a ((1-a)*lpNorm (fun x => g x*h x) ∞ μ *
      (∫ x, h x/g x ∂μ)/(∫ x, h x^2 ∂μ)))

private theorem actual_law : arena.{u}.Law actual := @fixed_weight.{u}
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  let Y := ULift.{u} Unit
  letI : MeasurableSpace Y := ⊤
  have he := @hh Y inferInstance Measure.count inferInstance inferInstance
    (fun _ => 1) (fun _ => 1) (memLp_top_const 1) (by simp) (one_weight _) 0 le_rfl zero_le_one
  have hn := he.1
  norm_num [rejected, realize] at hn

def family : Registration arena.{u} (type_of% (@fixed_weight.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    have hh := congrFun he 0
    norm_num [actual, realize] at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fixed_weight.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Semigroups.ConditionedRankOneNorm.Fixed.unit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.ConditionedRankOneNorm.Fixed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x+y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.ConditionedRankOneNorm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","arg","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Fixed

namespace Minimum
abbrev signature := Order.signature
abbrev actual := Order.actual
abbrev rejected := Order.rejected

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] [NeZero μ]
    {h : X → ℝ} (hh : MemLp h ∞ μ) (hp : ∀ᵐ x ∂μ, 0 < h x) {κ a : ℝ}
    (hκ : 1 ≤ κ) (ha : 0 ≤ a) (ha1 : a ≤ 1),
    Weight μ (clipped h (lpNorm h ∞ μ) κ) ∧
    R.readout () () (condition μ (clipped h (lpNorm h ∞ μ) κ)) κ ∧
    Sharp μ h a (clipped h (lpNorm h ∞ μ) κ) (optimum μ h a κ) ∧
    ∀ g : X → ℝ, Weight μ g → condition μ g ≤ κ →
      ∃ C : ℝ, Sharp μ h a g C ∧ optimum μ h a κ ≤ C ∧
        C - optimum μ h a κ = (1-a)/(∫ x, h x^2 ∂μ) *
          ∫ x, h x * |lpNorm (fun y => g y*h y) ∞ μ / g x -
            max (h x) (lpNorm h ∞ μ/κ)| ∂μ ∧
        (a < 1 → (C = optimum μ h a κ ↔ ∃ s : ℝ, 0 < s ∧
          g =ᵐ[μ] (fun x => s*clipped h (lpNorm h ∞ μ) κ x))) ∧
        (a = 1 → C = 1) ∧
        (a < 1 → (optimum μ h a κ = 1 ↔ ∀ᵐ x ∂μ, lpNorm h ∞ μ/κ ≤ h x))

private theorem actual_law : arena.{u}.Law actual := @conditioned_optimum.{u}
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  let Y := ULift.{u} Unit
  letI : MeasurableSpace Y := ⊤
  have he := @hh Y inferInstance Measure.count inferInstance inferInstance
    (fun _ => 1) (memLp_top_const 1) (by simp) 1 0 le_rfl le_rfl zero_le_one
  exact he.2.1

def family : Registration arena.{u} (type_of% (@conditioned_optimum.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    have hh : (1:ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@conditioned_optimum.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Semigroups.ConditionedRankOneNorm.Minimum.unit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.ConditionedRankOneNorm.Minimum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.ConditionedRankOneNorm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","arg","fn","arg","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Minimum

end Reg.D5.S3.Quantum.Semigroups.ConditionedRankOneNorm
