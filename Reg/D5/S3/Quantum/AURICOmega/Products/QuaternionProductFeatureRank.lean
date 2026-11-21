import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.Products.QuaternionProductFeatureRank
import Reg.Support.DependentFamily


/-! The number of factors determines the least dimension of the feature space. -/

namespace Reg.D5.S3.Quantum.AURICOmega.Products.QuaternionProductFeatureRank

open _root_.D5.S3.Quantum.AURICOmega.Products.QuaternionProductFeatureRank
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Quaternion InnerProductSpace

noncomputable section

namespace Dimension

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
  realize signature (fun _ _ n => 5 ^ n) (fun e => nomatch e)

def constant : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, IsLeast
    {d : ℕ | ∃ φ : (Fin n → unitary ℍ[ℝ]) → EuclideanSpace ℝ (Fin d),
      ∀ x y, productReading n x y = ⟪φ x, φ y⟫_ℝ} (r.readout () () n)

theorem rejected : ¬arena.Law constant := by
  intro h
  have heq := (least_feature_rank 1).unique (h 1)
  exact (by decide : (5 : ℕ) ^ 1 ≠ 1) heq

def source_registration : Registration arena (type_of% @least_feature_rank) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨least_feature_rank, constant, rejected⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨constant, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    exact ⟨(), 0, 1, by decide⟩

end Dimension

def least_feature_rank_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@least_feature_rank) (Realization Dimension.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.Products.QuaternionProductFeatureRank.least_feature_rank_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.Products.QuaternionProductFeatureRank.Dimension.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Dimension.arena⟩
  objectArena := .source ⟨Dimension.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Dimension.arena ⟨Dimension.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Dimension.signature (fun _ _ n => 5 ^ n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.Products.QuaternionProductFeatureRank
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.Products.QuaternionProductFeatureRank
