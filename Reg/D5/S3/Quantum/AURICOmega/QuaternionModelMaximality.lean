import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.QuaternionModelMaximality
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of the maximality of the unit-quaternion comparison model.

In all three theorems the readout is the model reading `kappa x y` that the copy `j` is required
to preserve, as a function of `y` with `x` as coordinate; the structure, the rank conditions, the
transfer condition and the bijectivity conclusion stay in the law verbatim. The rejected readout
is the constant reading one: the constant map onto one point of the unit quaternion comparison
model (lifted to an arbitrary universe where the theorem quantifies over one) preserves the
transfer, has constant reading one, lies in a structure of feature rank five, and is not
injective. -/

namespace Reg.D5.S3.Quantum.AURICOmega.QuaternionModelMaximality

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.QuaternionModelMaximality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
  (liftedModel liftedModel_hasFeatureRank_five one_ne_neg_one)
open LeanInformationAudit

open scoped InnerProductSpace Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u

/-! The model reading `kappa x y` against a fixed first argument. -/
namespace Reading

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (unitary ℍ[ℝ]) (fun _ => unitary ℍ[ℝ]) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p s => quaternionModel.kappa p s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, -1, fun e => ?_⟩
  change quaternionModel.kappa 1 1 = quaternionModel.kappa 1 (-1) at e
  rw [quaternionModel.kappa_self] at e
  exact one_ne_neg_one ((quaternionModel.kappa_eq_one_iff 1 (-1)).1 e.symm)

end Reading

/-! `bijective_of_hasFeatureRank_le_eight`. -/
namespace LeEight

/-- Retain the complete carrier, structure, rank, map and hypothesis telescope of
`bijective_of_hasFeatureRank_le_eight`; only the preserved model reading is read out. -/
abbrev arena : Arena where
  signature := Reading.signature
  Law rd := ∀ {M : Type u} (C : TernaryComparison M) {r : ℕ}, C.HasFeatureRank r → r ≤ 8 →
    ∀ (j : unitary ℍ[ℝ] → M),
      (∀ x y z, j (quaternionModel.tri x y z) = C.tri (j x) (j y) (j z)) →
      (∀ x y, C.kappa (j x) (j y) = rd.readout () x y) → Function.Bijective j

theorem rejected_law : ¬ arena.{u}.Law Reading.rejected := by
  intro h
  have hb := h liftedModel.{u} liftedModel_hasFeatureRank_five (by norm_num)
    (fun _ => ⟨1⟩) (fun _ _ _ => (liftedModel.tri_self_left _ _).symm)
    (fun _ _ => liftedModel.kappa_self _)
  exact one_ne_neg_one (@hb.1 1 (-1) rfl)

/-- The exact statement of `bijective_of_hasFeatureRank_le_eight`. -/
abbrev sourceStatement : Prop := type_of% @bijective_of_hasFeatureRank_le_eight.{u}

def source_registration : Registration arena.{u} sourceStatement.{u} where
  actual := Reading.actual
  bridge := Iff.rfl
  variation := ⟨@bijective_of_hasFeatureRank_le_eight.{u}, Reading.rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{u}.Law
    Reading.actual Reading.rejected rejected_law
  dependence := Reading.dependence

end LeEight

/-! `forall_bijective_iff_le_eight`. -/
namespace Sharp

/-- Retain the complete rank telescope and both sides of `forall_bijective_iff_le_eight`; only
the preserved model reading on the left is read out. -/
abbrev arena : Arena where
  signature := Reading.signature
  Law rd := ∀ r : ℕ,
    (∀ (M : Type) (C : TernaryComparison M) (j : unitary ℍ[ℝ] → M), C.HasFeatureRank r →
        (∀ x y z, j (quaternionModel.tri x y z) = C.tri (j x) (j y) (j z)) →
        (∀ x y, C.kappa (j x) (j y) = rd.readout () x y) → Function.Bijective j) ↔
      r ≤ 8

theorem rejected_law : ¬ arena.Law Reading.rejected := by
  intro h
  have hb := (h 5).mpr (by norm_num) (unitary ℍ[ℝ]) quaternionModel (fun _ => 1)
    quaternionModel_hasFeatureRank_five (fun _ _ _ => (quaternionModel.tri_self_left _ _).symm)
    (fun _ _ => quaternionModel.kappa_self _)
  exact one_ne_neg_one (@hb.1 1 (-1) rfl)

/-- The exact statement of `forall_bijective_iff_le_eight`. -/
abbrev sourceStatement : Prop := type_of% @forall_bijective_iff_le_eight

def source_registration : Registration arena sourceStatement where
  actual := Reading.actual
  bridge := Iff.rfl
  variation := ⟨@forall_bijective_iff_le_eight, Reading.rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    Reading.actual Reading.rejected rejected_law
  dependence := Reading.dependence

end Sharp

/-! `bijective_of_hasFeatureRank_five_of_kappa`. -/
namespace RankFive

/-- Retain the complete carrier, structure, rank, map and hypothesis telescope of
`bijective_of_hasFeatureRank_five_of_kappa`; only the preserved model reading is read out. -/
abbrev arena : Arena where
  signature := Reading.signature
  Law rd := ∀ {M : Type u} (C : TernaryComparison M), C.HasFeatureRank 5 →
    ∀ (j : unitary ℍ[ℝ] → M),
      (∀ x y, C.kappa (j x) (j y) = rd.readout () x y) → Function.Bijective j

theorem rejected_law : ¬ arena.{u}.Law Reading.rejected := by
  intro h
  have hb := h liftedModel.{u} liftedModel_hasFeatureRank_five (fun _ => ⟨1⟩)
    (fun _ _ => liftedModel.kappa_self _)
  exact one_ne_neg_one (@hb.1 1 (-1) rfl)

/-- The exact statement of `bijective_of_hasFeatureRank_five_of_kappa`. -/
abbrev sourceStatement : Prop := type_of% @bijective_of_hasFeatureRank_five_of_kappa.{u}

def source_registration : Registration arena.{u} sourceStatement.{u} where
  actual := Reading.actual
  bridge := Iff.rfl
  variation := ⟨@bijective_of_hasFeatureRank_five_of_kappa.{u}, Reading.rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{u}.Law
    Reading.actual Reading.rejected rejected_law
  dependence := Reading.dependence

end RankFive

def bijective_of_hasFeatureRank_le_eight_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bijective_of_hasFeatureRank_le_eight.{u}) (Realization Reading.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionModelMaximality.bijective_of_hasFeatureRank_le_eight_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionModelMaximality.LeEight.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨LeEight.arena.{u}⟩
  objectArena := .source ⟨LeEight.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source LeEight.arena.{u} ⟨LeEight.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Reading.signature
    (fun _ p s => quaternionModel.kappa p s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionModelMaximality
    definition := none
    coordinates := #[7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "domain", "body", "body",
        "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def forall_bijective_iff_le_eight_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@forall_bijective_iff_le_eight) (Realization Reading.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionModelMaximality.forall_bijective_iff_le_eight_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionModelMaximality.Sharp.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Sharp.arena⟩
  objectArena := .source ⟨Sharp.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Sharp.arena ⟨Sharp.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Reading.signature
    (fun _ p s => quaternionModel.kappa p s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionModelMaximality
    definition := none
    coordinates := #[6]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "body", "body", "body", "body", "domain", "body",
        "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def bijective_of_hasFeatureRank_five_of_kappa_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bijective_of_hasFeatureRank_five_of_kappa.{u}) (Realization Reading.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionModelMaximality.bijective_of_hasFeatureRank_five_of_kappa_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionModelMaximality.RankFive.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨RankFive.arena.{u}⟩
  objectArena := .source ⟨RankFive.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source RankFive.arena.{u} ⟨RankFive.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Reading.signature
    (fun _ p s => quaternionModel.kappa p s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionModelMaximality
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.AURICOmega.QuaternionModelMaximality
