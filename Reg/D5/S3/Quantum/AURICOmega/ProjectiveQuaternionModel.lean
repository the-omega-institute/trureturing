import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.ProjectiveQuaternionModel
import Reg.D5.S3.Quantum.AURICOmega.QuaternionProductRank
import Reg.Support.DependentFamily

/-! Source-bound audits of the projective quaternion comparison model: the reading of the
structure at a point and its first point of reading zero, as a function of the structure; and the
feature rank compared with the threshold ten, as a function of the rank. -/

namespace Reg.D5.S3.Quantum.AURICOmega.ProjectiveQuaternionModel

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.ProjectiveQuaternionModel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Quantum.AURICOmega.QuaternionProductRank (pullback)

open scoped InnerProductSpace Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

/-- The unit quaternion `a + b i + c j + d k` for `a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1`. -/
def unitQ (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) : unitary ℍ[ℝ] :=
  ⟨⟨a, b, c, d⟩, Unitary.mem_iff.mpr (by
    have hn : ((Quaternion.normSq (⟨a, b, c, d⟩ : ℍ[ℝ]) : ℝ) : ℍ[ℝ]) = 1 := by
      rw [Quaternion.normSq_def']
      change ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℝ) : ℍ[ℝ]) = 1
      rw [h, Quaternion.coe_one]
    exact ⟨(Quaternion.star_mul_self _).trans hn, (Quaternion.self_mul_star _).trans hn⟩)⟩

/-- The class of the unit quaternion `1`. -/
abbrev pointOne : ProjectiveQuaternion := QuotientGroup.mk (unitQ 1 0 0 0 (by norm_num))

/-- The class of the unit quaternion `i`. -/
abbrev pointI : ProjectiveQuaternion := QuotientGroup.mk (unitQ 0 1 0 0 (by norm_num))

/-- The class of the unit quaternion `(3 + 4 i) / 5`. -/
abbrev pointR : ProjectiveQuaternion := QuotientGroup.mk (unitQ (3 / 5) (4 / 5) 0 0 (by norm_num))

theorem kappa_one_i : projectiveModel.kappa pointOne pointI = 0 := by
  change ⟪((unitQ 1 0 0 0 _ : unitary ℍ[ℝ]) : ℍ[ℝ]), ((unitQ 0 1 0 0 _ : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ
    ^ 2 = 0
  simp [unitQ, inner_eq_components]

theorem kappa_r_i : projectiveModel.kappa pointR pointI = 16 / 25 := by
  change ⟪((unitQ (3 / 5) (4 / 5) 0 0 _ : unitary ℍ[ℝ]) : ℍ[ℝ]),
    ((unitQ 0 1 0 0 _ : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ ^ 2 = 16 / 25
  simp [unitQ, inner_eq_components]
  norm_num

theorem pointI_ne_pointOne : pointI ≠ pointOne := by
  intro h
  have h1 := kappa_one_i
  rw [h, projectiveModel.kappa_self] at h1
  norm_num at h1

theorem pointI_ne_pointR : pointI ≠ pointR := by
  intro h
  have h1 := kappa_r_i
  rw [h, projectiveModel.kappa_self] at h1
  norm_num at h1

open Classical in
/-- The projective model transported along the transposition of the classes of `1` and
`(3 + 4 i) / 5`. -/
def swappedModel : TernaryComparison ProjectiveQuaternion :=
  pullback (Equiv.swap pointOne pointR) projectiveModel

theorem swappedModel_kappa : swappedModel.kappa pointOne pointI = 16 / 25 := by
  classical
  change projectiveModel.kappa (Equiv.swap pointOne pointR pointOne)
    (Equiv.swap pointOne pointR pointI) = 16 / 25
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne pointI_ne_pointOne pointI_ne_pointR]
  exact kappa_r_i

namespace ZeroReading

/-- Observe the reading of a structure on the unit quaternions modulo sign at a pair of points. -/
abbrev signature : Signature where
  Params := Σ _ : ProjectiveQuaternion, ProjectiveQuaternion
  State _ := TernaryComparison ProjectiveQuaternion
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q C => C.kappa q.1 q.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Retain all six conjuncts of `projectiveModel_featureRank_ten`; the reading at the first
point of reading zero is observed as a function of the structure. -/
abbrev arena : Arena where
  signature := signature
  Law r := projectiveModel.Noncommutative ∧ projectiveModel.ChainConnected ∧
    projectiveModel.TouchesZero ∧ ReadingComplete projectiveModel ∧
    (∀ r : ℕ, projectiveModel.HasFeatureRank r ↔ 10 ≤ r) ∧
    ∀ p : ProjectiveQuaternion, ∃ a b : ProjectiveQuaternion, a ≠ b ∧
      r.readout () ⟨p, a⟩ projectiveModel = 0 ∧ projectiveModel.kappa p b = 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, b, -, ha, -⟩ := h.2.2.2.2.2 pointOne
  change (1 : ℝ) = 0 at ha
  exact one_ne_zero ha

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨pointOne, pointI⟩, projectiveModel, swappedModel, fun h => ?_⟩
  change projectiveModel.kappa pointOne pointI = swappedModel.kappa pointOne pointI at h
  rw [kappa_one_i, swappedModel_kappa] at h
  norm_num at h

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @projectiveModel_featureRank_ten

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@projectiveModel_featureRank_ten, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end ZeroReading

/-! The rank `r` compared with the threshold in `10 ≤ r` inside
`∀ r : ℕ, projectiveModel.HasFeatureRank r ↔ 10 ≤ r`, read from its binder. -/
namespace RankThreshold

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

/-- Shifting the compared rank by one would move the least feature rank from ten to nine. -/
def rejected : Realization signature :=
  realize signature (fun _ _ s => s + 1) (fun e => nomatch e)

/-- Retain all six conjuncts of `projectiveModel_featureRank_ten`; the rank compared with ten is
observed as a function of the rank. -/
abbrev arena : Arena where
  signature := signature
  Law rd := projectiveModel.Noncommutative ∧ projectiveModel.ChainConnected ∧
    projectiveModel.TouchesZero ∧ ReadingComplete projectiveModel ∧
    (∀ r : ℕ, projectiveModel.HasFeatureRank r ↔ 10 ≤ rd.readout () () r) ∧
    ∀ p : ProjectiveQuaternion, ∃ a b : ProjectiveQuaternion, a ≠ b ∧
      projectiveModel.kappa p a = 0 ∧ projectiveModel.kappa p b = 0

/-- With the shifted readout the structure would have feature rank nine, which it has not. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h9 : projectiveModel.HasFeatureRank 9 := (h.2.2.2.2.1 9).mpr (by
    change 10 ≤ 9 + 1
    norm_num)
  have h10 := (projectiveModel_featureRank_ten.2.2.2.2.1 9).mp h9
  norm_num at h10

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, fun h => ?_⟩
  change (0 : ℕ) = 1 at h
  exact absurd h (by norm_num)

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @projectiveModel_featureRank_ten

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@projectiveModel_featureRank_ten, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end RankThreshold

def projectiveModel_featureRank_ten_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@projectiveModel_featureRank_ten) (Realization ZeroReading.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.ProjectiveQuaternionModel.projectiveModel_featureRank_ten_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.ProjectiveQuaternionModel.ZeroReading.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨ZeroReading.arena⟩
  objectArena := .source ⟨ZeroReading.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ZeroReading.arena ⟨ZeroReading.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ZeroReading.signature
    (fun _ q C => C.kappa q.1 q.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.ProjectiveQuaternionModel
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "arg", "body", "arg", "body", "arg", "body",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def projectiveModel_featureRank_ten_rank_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@projectiveModel_featureRank_ten) (Realization RankThreshold.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.ProjectiveQuaternionModel.projectiveModel_featureRank_ten_rank_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.ProjectiveQuaternionModel.RankThreshold.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨RankThreshold.arena⟩
  objectArena := .source ⟨RankThreshold.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source RankThreshold.arena ⟨RankThreshold.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize RankThreshold.signature (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.ProjectiveQuaternionModel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "fn", "arg", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.ProjectiveQuaternionModel
