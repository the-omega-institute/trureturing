import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
import Reg.Support.DependentFamily

/-! Source-bound audit of the closed-subgroup theorem for the unit quaternions.

The whole group is a closed subgroup that is chain connected for the reading of the quaternion
comparison model and noncommutative, so it satisfies every hypothesis of the theorem. The rejected
law fails there because the whole group is not the trivial subgroup. -/

namespace Reg.D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive (one_ne_neg_one)

open scoped Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

/-- The whole group is closed. -/
theorem isClosed_top : IsClosed ((⊤ : Subgroup (unitary ℍ[ℝ])) : Set (unitary ℍ[ℝ])) := by
  rw [Subgroup.coe_top]
  exact isClosed_univ

/-- Any two unit quaternions are joined by a chain with consecutive readings above `1 - ε`. -/
theorem chain_top (ε : ℝ) (hε : 0 < ε) (x : unitary ℍ[ℝ]) (_ : x ∈ (⊤ : Subgroup (unitary ℍ[ℝ])))
    (y : unitary ℍ[ℝ]) (_ : y ∈ (⊤ : Subgroup (unitary ℍ[ℝ]))) :
    Relation.ReflTransGen (fun a b : unitary ℍ[ℝ] =>
      b ∈ (⊤ : Subgroup (unitary ℍ[ℝ])) ∧ 1 - ε < quaternionModel.kappa a b) x y :=
  Relation.ReflTransGen.mono (fun _ b h => ⟨Subgroup.mem_top b, h⟩) _ _
    (quaternionModel_chainConnected ε hε x y)

/-- The whole group contains two noncommuting elements. -/
theorem noncomm_top : ∃ x ∈ (⊤ : Subgroup (unitary ℍ[ℝ])),
    ∃ y ∈ (⊤ : Subgroup (unitary ℍ[ℝ])), x * y ≠ y * x := by
  obtain ⟨x, y, hxy⟩ := (quaternionModel.noncommutative_iff 1).mp quaternionModel_noncommutative
  refine ⟨x, Subgroup.mem_top x, y, Subgroup.mem_top y, fun h => hxy ?_⟩
  change x * 1⁻¹ * y = y * 1⁻¹ * x
  rw [inv_one, mul_one, mul_one, h]

/-- The whole group is not the trivial subgroup. -/
theorem bot_ne_top_unitary : (⊥ : Subgroup (unitary ℍ[ℝ])) ≠ ⊤ := by
  intro h
  have hm : (-1 : unitary ℍ[ℝ]) ∈ (⊥ : Subgroup (unitary ℍ[ℝ])) := h ▸ Subgroup.mem_top _
  exact one_ne_neg_one (Subgroup.mem_bot.mp hm).symm

/-! The subgroup `H` on the left of the conclusion `H = ⊤` of
`eq_top_of_isClosed_of_chainConnected`, read from its binder. -/
namespace Whole

abbrev signature : Signature where
  Params := Unit
  State _ := Subgroup (unitary ℍ[ℝ])
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Subgroup (unitary ℍ[ℝ])
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

/-- Retain the complete subgroup, closedness, chain and noncommutativity telescope of
`eq_top_of_isClosed_of_chainConnected`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ H : Subgroup (unitary ℍ[ℝ]), IsClosed (H : Set (unitary ℍ[ℝ])) →
    (∀ ε : ℝ, 0 < ε → ∀ x ∈ H, ∀ y ∈ H,
      Relation.ReflTransGen
        (fun a b : unitary ℍ[ℝ] => b ∈ H ∧ 1 - ε < quaternionModel.kappa a b) x y) →
    (∃ x ∈ H, ∃ y ∈ H, x * y ≠ y * x) → r.readout () () H = ⊤

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact bot_ne_top_unitary (h ⊤ isClosed_top chain_top noncomm_top)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨(), ⊤, ⊥, fun e => bot_ne_top_unitary e.symm⟩

def source_registration :
    Registration arena (type_of% @eq_top_of_isClosed_of_chainConnected) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eq_top_of_isClosed_of_chainConnected, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Whole

def eq_top_of_isClosed_of_chainConnected_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@eq_top_of_isClosed_of_chainConnected) (Realization Whole.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup.eq_top_of_isClosed_of_chainConnected_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup.Whole.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Whole.arena⟩
  objectArena := .source ⟨Whole.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Whole.arena ⟨Whole.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Whole.signature (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup
