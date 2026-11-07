import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.OrderUnitCompletion

/-! The comparison readout retains the complete faithful-completion source telescope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Topology.OrderUnitCompletion

open _root_.D5.S3.Topology.OrderUnitNorm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit UniformSpace Set
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Data E) (hnorm : ∀ a : E, ‖a‖ = A.orderNorm a),
    (∀ x : Completion E, ∀ r : ℝ, R.readout () () ‖x‖ r ↔
      0 ≤ r ∧ r • (A.completedData hnorm).unit - x ∈ (A.completedData hnorm).cone ∧
        r • (A.completedData hnorm).unit + x ∈ (A.completedData hnorm).cone) ∧
    (∀ x : Completion E, (A.completedData hnorm).orderNorm x = ‖x‖) ∧
    (∀ a : E, (Completion.toComplₗᵢ (𝕜 := ℝ) (E := E)) a ∈
      (A.completedData hnorm).cone ↔ a ∈ A.cone)

private theorem actual_law : arena.{u}.Law actual := @Data.faithful_completion.{u}

private def zeroData : Data PUnit.{u+1} where
  cone := ⊤
  unit := 0
  zero_mem := by trivial
  closed := isClosed_univ
  salient := by
    intro x hx hne
    exact (hne (Subsingleton.elim _ _)).elim
  interior_unit := by simp

private theorem zeroNorm : ∀ a : PUnit.{u+1}, ‖a‖ = zeroData.orderNorm a := by
  intro a
  have h := (zeroData.norm_le_iff a (zeroData.orderNorm a)).mp le_rfl
  have hz : zeroData.orderNorm a ≤ 0 :=
    (zeroData.norm_le_iff a 0).mpr ⟨le_rfl, by trivial, by trivial⟩
  have ha : a = 0 := Subsingleton.elim _ _
  calc
    ‖a‖ = 0 := by simp [ha]
    _ = zeroData.orderNorm a := (le_antisymm hz h.1).symm

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h zeroData zeroNorm).1 (0 : Completion PUnit.{u+1}) 0
  have hz : (0 : Completion PUnit.{u+1}) ∈
      (zeroData.{u}.completedData zeroNorm.{u}).cone := Data.zero_mem _
  exact hh.mpr ⟨le_rfl, by simpa using hz, by simpa using hz⟩

def family : Registration arena.{u} (type_of% (@Data.faithful_completion.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hb : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hb

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@Data.faithful_completion.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Topology.OrderUnitNorm.Data.faithfulCompletionUnit
  realizationName := `Reg.D5.S3.Topology.OrderUnitCompletion.family
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
    owner := `D5.S3.Topology.OrderUnitCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "body",
        "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.OrderUnitCompletion
