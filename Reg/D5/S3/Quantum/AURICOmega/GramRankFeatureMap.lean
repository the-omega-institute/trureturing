import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.GramRankFeatureMap
import Reg.Support.DependentFamily

/-! Source-bound audits of the equivalence between finite Gram rank and Euclidean feature maps
and of the monotonicity of feature rank.

For the equivalence, the audited observation is the rank bound handed to the Gram side; for the
monotonicity, it is the target rank in the conclusion. The model used for both rejected laws is
the one-point comparison structure. -/

namespace Reg.D5.S3.Quantum.AURICOmega.GramRankFeatureMap

open _root_.D5.S3.Quantum.AURICOmega.GramRankFeatureMap
open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u

/-- The one-point structure: constant transfer and constant reading one. -/
def onePoint : TernaryComparison (ULift.{u} Unit) where
  tri _ _ _ := ⟨()⟩
  kappa _ _ := 1
  tri_self_left _ _ := Subsingleton.elim _ _
  tri_self_right _ _ := Subsingleton.elim _ _
  tri_assoc _ _ _ _ _ := rfl
  kappa_symm _ _ := rfl
  kappa_eq_one_iff x y := ⟨fun _ => Subsingleton.elim x y, fun _ => rfl⟩
  kappa_nonneg _ _ := zero_le_one
  kappa_tri_right _ _ _ _ := rfl
  kappa_tri_left _ _ _ _ := rfl
  kappa_gram_nonneg n x c := by
    have key : ∑ i, ∑ j, c i * c j * (1 : ℝ) = (∑ i, c i) * (∑ j, c j) := by
      rw [Finset.sum_mul_sum]
      simp
    rw [key]
    exact mul_self_nonneg _

theorem onePoint_hasFeatureRank_one : onePoint.{u}.HasFeatureRank 1 := by
  refine ⟨fun _ => EuclideanSpace.single 0 1, fun x y => ?_⟩
  change (1 : ℝ) = ⟪EuclideanSpace.single (0 : Fin 1) (1 : ℝ), EuclideanSpace.single 0 1⟫_ℝ
  simp

theorem onePoint_not_hasFeatureRank_zero : ¬ onePoint.{u}.HasFeatureRank 0 := by
  rintro ⟨φ, hφ⟩
  have h := hφ ⟨()⟩ ⟨()⟩
  change (1 : ℝ) = ⟪φ ⟨()⟩, φ ⟨()⟩⟫_ℝ at h
  rw [Subsingleton.elim (φ ⟨()⟩) 0, inner_zero_left] at h
  exact one_ne_zero h

/-! The rank bound read on the Gram side of the equivalence. -/
namespace RankBound

abbrev signature : Signature where
  Params := Σ M : Type u, TernaryComparison M
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

def constant : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete carrier, structure and rank telescope of
`gramRankLE_iff_hasFeatureRank`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {M : Type u} (C : TernaryComparison M) (k : ℕ),
    C.GramRankLE (r.readout () ⟨M, C⟩ k) ↔ C.HasFeatureRank k

theorem rejected_law : ¬ arena.{u}.Law constant := by
  intro h
  have h1 := (h onePoint.{u} 1).2 onePoint_hasFeatureRank_one
  exact onePoint_not_hasFeatureRank_zero
    ((gramRankLE_iff_hasFeatureRank onePoint.{u} 0).1 h1)

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  exact ⟨⟨ULift.{u} Unit, onePoint⟩, 0, 1, by decide⟩

def source_registration :
    Registration arena.{u} (type_of% @gramRankLE_iff_hasFeatureRank.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@gramRankLE_iff_hasFeatureRank.{u}, constant, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨constant, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end RankBound

def gramRankLE_iff_hasFeatureRank_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@gramRankLE_iff_hasFeatureRank.{u}) (Realization RankBound.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.GramRankFeatureMap.gramRankLE_iff_hasFeatureRank_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.GramRankFeatureMap.RankBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨RankBound.arena.{u}⟩
  objectArena := .source ⟨RankBound.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source RankBound.arena.{u} ⟨RankBound.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize RankBound.signature.{u} (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.GramRankFeatureMap
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-! The target rank `s` in the conclusion `C.HasFeatureRank s` of `hasFeatureRank_mono`; the
rejected reading `0` fails on the one-point structure, which has feature rank one but not zero. -/
namespace MonoBound

def actual : Realization RankBound.signature.{u} :=
  realize RankBound.signature (fun _ _ s => s) (fun e => nomatch e)

def constant : Realization RankBound.signature.{u} :=
  realize RankBound.signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete carrier, structure, rank and hypothesis telescope of
`hasFeatureRank_mono`. -/
abbrev arena : Arena where
  signature := RankBound.signature.{u}
  Law rd := ∀ {M : Type u} {C : TernaryComparison M} {r s : ℕ}, r ≤ s → C.HasFeatureRank r →
    C.HasFeatureRank (rd.readout () ⟨M, C⟩ s)

theorem rejected_law : ¬ arena.{u}.Law constant := fun h =>
  onePoint_not_hasFeatureRank_zero (h (C := onePoint.{u}) (le_refl 1) onePoint_hasFeatureRank_one)

theorem dependence : ObservationalDependence RankBound.signature.{u} actual := by
  intro i
  cases i
  exact ⟨⟨ULift.{u} Unit, onePoint⟩, 0, 1, by decide⟩

abbrev sourceStatement : Prop := type_of% @hasFeatureRank_mono.{u}

def source_registration : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hasFeatureRank_mono.{u}, constant, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨constant, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end MonoBound

def hasFeatureRank_mono_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@hasFeatureRank_mono.{u}) (Realization RankBound.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.GramRankFeatureMap.hasFeatureRank_mono_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.GramRankFeatureMap.MonoBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨MonoBound.arena.{u}⟩
  objectArena := .source ⟨MonoBound.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source MonoBound.arena.{u} ⟨MonoBound.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize RankBound.signature.{u} (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.GramRankFeatureMap
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.GramRankFeatureMap
