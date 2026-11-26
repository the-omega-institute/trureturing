import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import Reg.Support.DependentFamily

/-! Source-bound audits of the feature-rank bound and the unit quaternion embedding.

Both rejected laws are refuted on the unit quaternion comparison model, lifted to an arbitrary
universe; the lifted model is noncommutative, chain connected, touches zero and has feature
rank five, so it satisfies every hypothesis of both theorems. -/

namespace Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open scoped InnerProductSpace Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u

/-- The unit quaternion comparison model, carried to `ULift (unitary ℍ)`. -/
def liftedModel : TernaryComparison (ULift.{u} (unitary ℍ[ℝ])) where
  tri x y z := ⟨quaternionModel.tri x.down y.down z.down⟩
  kappa x y := quaternionModel.kappa x.down y.down
  tri_self_left x z := congrArg ULift.up (quaternionModel.tri_self_left x.down z.down)
  tri_self_right x z := congrArg ULift.up (quaternionModel.tri_self_right x.down z.down)
  tri_assoc x y z u v :=
    congrArg ULift.up (quaternionModel.tri_assoc x.down y.down z.down u.down v.down)
  kappa_symm x y := quaternionModel.kappa_symm x.down y.down
  kappa_eq_one_iff x y :=
    (quaternionModel.kappa_eq_one_iff x.down y.down).trans ULift.ext_iff.symm
  kappa_nonneg x y := quaternionModel.kappa_nonneg x.down y.down
  kappa_tri_right x y u v := quaternionModel.kappa_tri_right x.down y.down u.down v.down
  kappa_tri_left u v x y := quaternionModel.kappa_tri_left u.down v.down x.down y.down
  kappa_gram_nonneg n x c := quaternionModel.kappa_gram_nonneg n (fun i => (x i).down) c

theorem liftedModel_noncommutative : liftedModel.{u}.Noncommutative := by
  obtain ⟨x, y, z, h⟩ := quaternionModel_noncommutative
  exact ⟨⟨x⟩, ⟨y⟩, ⟨z⟩, fun e => h (congrArg ULift.down e)⟩

theorem liftedModel_chainConnected : liftedModel.{u}.ChainConnected := by
  intro ε hε x y
  exact Relation.ReflTransGen.lift ULift.up (fun _ _ h => h) x.down y.down
    (quaternionModel_chainConnected ε hε x.down y.down)

theorem liftedModel_touchesZero : liftedModel.{u}.TouchesZero := by
  intro ε hε
  obtain ⟨x, y, h⟩ := quaternionModel_touchesZero ε hε
  exact ⟨⟨x⟩, ⟨y⟩, h⟩

theorem liftedModel_hasFeatureRank_five : liftedModel.{u}.HasFeatureRank 5 := by
  obtain ⟨φ, hφ⟩ := quaternionModel_hasFeatureRank_five
  exact ⟨fun x => φ x.down, fun x y => hφ x.down y.down⟩

theorem one_ne_neg_one : (1 : unitary ℍ[ℝ]) ≠ -1 := by
  intro h
  have h1 := congrArg (fun q : unitary ℍ[ℝ] => (q : ℍ[ℝ]).re) h
  change ((1 : unitary ℍ[ℝ]) : ℍ[ℝ]).re = ((-1 : unitary ℍ[ℝ]) : ℍ[ℝ]).re at h1
  rw [Unitary.coe_neg, OneMemClass.coe_one, Quaternion.re_neg, Quaternion.re_one] at h1
  norm_num at h1

/-! The rank `r` in the conclusion `5 ≤ r` of `five_le_of_hasFeatureRank`, read from its binder. -/
namespace FeatureBound

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

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete carrier, structure, hypothesis and rank telescope of
`five_le_of_hasFeatureRank`. -/
abbrev arena : Arena where
  signature := signature
  Law rd := ∀ {M : Type u} (C : TernaryComparison M), C.Noncommutative → C.ChainConnected →
    ∀ r : ℕ, C.HasFeatureRank r → 5 ≤ rd.readout () () r

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h liftedModel.{u} liftedModel_noncommutative liftedModel_chainConnected 5
    liftedModel_hasFeatureRank_five
  exact absurd hh (by decide)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 5, 0, ?_⟩
  decide

def source_registration :
    Registration arena.{u} (type_of% @five_le_of_hasFeatureRank.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@five_le_of_hasFeatureRank.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end FeatureBound

/-! The transfer inside `u (C.tri x y z)` of `exists_unitQuaternion_embedding`, against its
first two arguments. -/
namespace Embedding

abbrev signature : Signature where
  Params := Σ M : Type u, Σ _ : TernaryComparison M, Σ _ : M, M
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => p.2.1.tri p.2.2.1 p.2.2.2 s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

/-- Retain the complete carrier, structure and hypothesis telescope and both conjuncts of
`exists_unitQuaternion_embedding`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law rd := ∀ {M : Type u} (C : TernaryComparison M), C.Noncommutative → C.ChainConnected →
    C.TouchesZero → C.HasFeatureRank 5 →
    ∃ u : M → unitary ℍ[ℝ], Function.Injective u ∧
      (∀ x y z : M, u (rd.readout () ⟨M, C, x, y⟩ z) = u x * (u y)⁻¹ * u z) ∧
      (∀ x y : M, C.kappa x y = (1 + ⟪(u x : ℍ[ℝ]), (u y : ℍ[ℝ])⟫_ℝ) / 2)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨w, hinj, htri, -⟩ := h liftedModel.{u} liftedModel_noncommutative
    liftedModel_chainConnected liftedModel_touchesZero liftedModel_hasFeatureRank_five
  have hh : w ⟨1⟩ = w ⟨1⟩ * (w ⟨-1⟩)⁻¹ * w ⟨1⟩ := htri ⟨1⟩ ⟨-1⟩ ⟨1⟩
  rw [mul_assoc] at hh
  have h1 : (w ⟨-1⟩)⁻¹ * w ⟨1⟩ = 1 := by
    have h2 := congrArg (fun a => (w ⟨1⟩)⁻¹ * a) hh
    simpa only [inv_mul_cancel_left, inv_mul_cancel] using h2.symm
  have h3 : w ⟨-1⟩ = w ⟨1⟩ := inv_mul_eq_one.mp h1
  exact one_ne_neg_one (congrArg ULift.down (hinj h3)).symm

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨ULift.{u} (unitary ℍ[ℝ]), liftedModel, ⟨1⟩, ⟨1⟩⟩, ⟨1⟩, ⟨-1⟩, ?_⟩
  change liftedModel.tri ⟨1⟩ ⟨1⟩ ⟨1⟩ ≠ liftedModel.tri ⟨1⟩ ⟨1⟩ ⟨-1⟩
  rw [liftedModel.tri_self_left, liftedModel.tri_self_left]
  exact fun e => one_ne_neg_one (congrArg ULift.down e)

def source_registration :
    Registration arena.{u} (type_of% @exists_unitQuaternion_embedding.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_unitQuaternion_embedding.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Embedding

def five_le_of_hasFeatureRank_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@five_le_of_hasFeatureRank.{u}) (Realization FeatureBound.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive.five_le_of_hasFeatureRank_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive.FeatureBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨FeatureBound.arena.{u}⟩
  objectArena := .source ⟨FeatureBound.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source FeatureBound.arena.{u} ⟨FeatureBound.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize FeatureBound.signature (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def exists_unitQuaternion_embedding_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_unitQuaternion_embedding.{u}) (Realization Embedding.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive.exists_unitQuaternion_embedding_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive.Embedding.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Embedding.arena.{u}⟩
  objectArena := .source ⟨Embedding.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Embedding.arena.{u} ⟨Embedding.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize Embedding.signature.{u} (fun _ p s => p.2.1.tri p.2.2.1 p.2.2.2 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
    definition := none
    coordinates := #[0, 1, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn",
        "arg", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
