import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.TernaryComparisonCompletion
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
import Reg.Support.DependentFamily

/-! Source-bound audits of the reading-completion theorems for ternary comparison structures.

The density criterion is read at the map `v` inside `DenseRange v`; the unit quaternion
comparison model lifted to an arbitrary universe, with `v = ULift.down`, satisfies both
hypotheses and both sides, and a constant map into the unit quaternions does not have dense
range. The closedness criterion is read at the underlying set of the subgroup in `IsClosed`: the
whole group is closed and the set of unit quaternions other than one is not. The independence
statement is read at the subgroup inside its last clause: the whole group of unit quaternions has
complete reading. -/

namespace Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonCompletion

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism
open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
  (liftedModel liftedModel_noncommutative liftedModel_chainConnected one_ne_neg_one)

open scoped Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u

/-- A constant map into the unit quaternions does not have dense range: the closure of a point
is the point, and `-1 ≠ 1`. -/
theorem not_denseRange_const {α : Type*} [Nonempty α] :
    ¬ DenseRange (fun _ : α => (1 : unitary ℍ[ℝ])) := by
  intro h
  have hc := h.closure_range
  rw [Set.range_const, closure_singleton] at hc
  have hm : (-1 : unitary ℍ[ℝ]) ∈ ({1} : Set (unitary ℍ[ℝ])) := by
    rw [hc]
    trivial
  exact one_ne_neg_one (Set.mem_singleton_iff.mp hm).symm

/-- The whole group of unit quaternions is closed. -/
theorem isClosed_top : IsClosed ((⊤ : Subgroup (unitary ℍ[ℝ])) : Set (unitary ℍ[ℝ])) := by
  rw [Subgroup.coe_top]
  exact isClosed_univ

/-- The unit quaternions other than one do not form a closed set: the complement of a point is
open, and the unit three-sphere is connected. -/
theorem not_isClosed_compl_one : ¬ IsClosed ({1}ᶜ : Set (unitary ℍ[ℝ])) := by
  intro hc
  have : PreconnectedSpace (unitary ℍ[ℝ]) := Subtype.preconnectedSpace (by
    rw [coe_unitary_eq_sphere]
    exact isPreconnected_sphere (by rw [Quaternion.rank_eq_four]; norm_num) 0 1)
  rcases isClopen_iff.mp ⟨hc, isOpen_compl_singleton⟩ with h | h
  · have hm : (-1 : unitary ℍ[ℝ]) ∈ ({1}ᶜ : Set (unitary ℍ[ℝ])) :=
      fun e => one_ne_neg_one (Set.mem_singleton_iff.mp e).symm
    rw [h] at hm
    exact hm
  · have hm : (1 : unitary ℍ[ℝ]) ∈ ({1}ᶜ : Set (unitary ℍ[ℝ])) := by
      rw [h]
      trivial
    exact hm rfl

/-- The trivial subgroup and the whole group of unit quaternions are different. -/
theorem bot_ne_top_unitary : (⊥ : Subgroup (unitary ℍ[ℝ])) ≠ ⊤ := by
  intro h
  have hm : (-1 : unitary ℍ[ℝ]) ∈ (⊥ : Subgroup (unitary ℍ[ℝ])) := h ▸ Subgroup.mem_top _
  exact one_ne_neg_one (Subgroup.mem_bot.mp hm).symm

/-! The map `v` inside `DenseRange v` of `denseRange_iff`, read from its binder. -/
namespace DenseCriterion

abbrev signature : Signature where
  Params := Type u
  State M := M → unitary ℍ[ℝ]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ M := M → unitary ℍ[ℝ]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => fun _ => 1) (fun e => nomatch e)

/-- Retain the complete carrier, structure, map and hypothesis telescope and both sides of the
equivalence of `denseRange_iff`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law rd := ∀ {M : Type u} (C : TernaryComparison M) (v : M → unitary ℍ[ℝ]),
    (∀ x y z, v (C.tri x y z) = quaternionModel.tri (v x) (v y) (v z)) →
    (∀ x y, C.kappa x y = quaternionModel.kappa (v x) (v y)) →
    (DenseRange (rd.readout () M v) ↔ C.Noncommutative ∧ C.ChainConnected)

/-- On the lifted unit quaternion model with `v = ULift.down` the right side holds, while a
constant map does not have dense range. -/
theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hd := (h liftedModel.{u} ULift.down (fun _ _ _ => rfl) (fun _ _ => rfl)).mpr
    ⟨liftedModel_noncommutative, liftedModel_chainConnected⟩
  change DenseRange (fun _ : ULift.{u} (unitary ℍ[ℝ]) => (1 : unitary ℍ[ℝ])) at hd
  exact not_denseRange_const hd

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨PUnit.{u + 1}, fun _ => 1, fun _ => -1, fun h => ?_⟩
  change (fun _ : PUnit.{u + 1} => (1 : unitary ℍ[ℝ])) = fun _ => -1 at h
  exact one_ne_neg_one (congrFun h PUnit.unit)

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @denseRange_iff.{u}

def source_registration : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@denseRange_iff.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end DenseCriterion

/-! The underlying set `(H : Set (unitary ℍ[ℝ]))` of a subgroup `H`, as a function of `H`. -/
namespace Carrier

abbrev signature : Signature where
  Params := Unit
  State _ := Subgroup (unitary ℍ[ℝ])
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set (unitary ℍ[ℝ])
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => (s : Set (unitary ℍ[ℝ]))) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), ⊤, ⊥, fun h => ?_⟩
  change ((⊤ : Subgroup (unitary ℍ[ℝ])) : Set (unitary ℍ[ℝ])) =
    ((⊥ : Subgroup (unitary ℍ[ℝ])) : Set (unitary ℍ[ℝ])) at h
  exact bot_ne_top_unitary (SetLike.coe_injective h).symm

end Carrier

/-! The underlying set of `H` inside `IsClosed` in `subgroupModel_readingComplete_iff`. -/
namespace Closedness

def rejected : Realization Carrier.signature :=
  realize Carrier.signature (fun _ _ _ => ({1}ᶜ : Set (unitary ℍ[ℝ]))) (fun e => nomatch e)

/-- Retain the complete subgroup telescope and both sides of
`subgroupModel_readingComplete_iff`. -/
abbrev arena : Arena where
  signature := Carrier.signature
  Law r := ∀ H : Subgroup (unitary ℍ[ℝ]),
    ReadingComplete (subgroupModel H) ↔ IsClosed (r.readout () () H)

theorem rejected_law : ¬ arena.Law rejected := fun h =>
  not_isClosed_compl_one ((h ⊤).1 ((subgroupModel_readingComplete_iff ⊤).2 isClosed_top))

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @subgroupModel_readingComplete_iff

def source_registration : Registration arena sourceStatement where
  actual := Carrier.actual
  bridge := Iff.rfl
  variation := ⟨@subgroupModel_readingComplete_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := Carrier.dependence

end Closedness

/-! The subgroup `H` inside `¬ ReadingComplete (subgroupModel H)` in
`exists_subgroupModel_not_readingComplete`, read from its existential binder. -/
namespace Incomplete

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
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

/-- Retain the existential subgroup and all five conjuncts of
`exists_subgroupModel_not_readingComplete`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∃ H : Subgroup (unitary ℍ[ℝ]),
    (subgroupModel H).Noncommutative ∧ (subgroupModel H).ChainConnected ∧
      (subgroupModel H).TouchesZero ∧ (subgroupModel H).HasFeatureRank 5 ∧
      ¬ ReadingComplete (subgroupModel (r.readout () () H))

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨_, -, -, -, -, h⟩
  exact h ((subgroupModel_readingComplete_iff ⊤).2 isClosed_top)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨(), ⊥, ⊤, bot_ne_top_unitary⟩

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @exists_subgroupModel_not_readingComplete

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_subgroupModel_not_readingComplete, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Incomplete

def denseRange_iff_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@denseRange_iff.{u}) (Realization DenseCriterion.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonCompletion.denseRange_iff_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonCompletion.DenseCriterion.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨DenseCriterion.arena.{u}⟩
  objectArena := .source ⟨DenseCriterion.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source DenseCriterion.arena.{u} ⟨DenseCriterion.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize DenseCriterion.signature.{u} (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonCompletion
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def subgroupModel_readingComplete_iff_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@subgroupModel_readingComplete_iff) (Realization Carrier.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonCompletion.subgroupModel_readingComplete_iff_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonCompletion.Closedness.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Closedness.arena⟩
  objectArena := .source ⟨Closedness.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Closedness.arena ⟨Closedness.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Carrier.signature
    (fun _ _ s => (s : Set (unitary ℍ[ℝ]))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def exists_subgroupModel_not_readingComplete_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_subgroupModel_not_readingComplete) (Realization Incomplete.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonCompletion.exists_subgroupModel_not_readingComplete_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonCompletion.Incomplete.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Incomplete.arena⟩
  objectArena := .source ⟨Incomplete.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Incomplete.arena ⟨Incomplete.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Incomplete.signature (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonCompletion
