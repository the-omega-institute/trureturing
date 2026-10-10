import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.GoldenResource.ActualOptimizerPrimeLoss
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenResource.ActualOptimizerPrimeLoss

open _root_.D5.S3.Arith.GoldenResource.ActualOptimizerPrimeLoss
open _root_.D5.S3.Arith.GoldenResource.GoldenSmallestMissingPrime
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => goldenLayerMarginal p 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ p => goldenLayerMarginal p 1 + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ p : ℕ, p.Prime →
    price (p + 1) < r.readout () p ∧ r.readout () p < price p

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 (by decide)
  change price (2 + 1) < goldenLayerMarginal 2 1 + 1 ∧
    goldenLayerMarginal 2 1 + 1 < price 2 at hh
  have hp := (first_layer_between_prices (by decide : Nat.Prime 2)).2
  linarith

def familyRegistration : Registration arena
    (∀ p : ℕ, p.Prime →
      price (p + 1) < goldenLayerMarginal p 1 ∧ goldenLayerMarginal p 1 < price p) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨first_layer_between_prices, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 2, 3, ?_⟩
    change goldenLayerMarginal 2 1 ≠ goldenLayerMarginal 3 1
    exact (golden_layer_marginal_one_strictAnti (by decide) (by decide) (by decide)).ne

def registration : LeanInformationAudit.Contract.Registration
    (@first_layer_between_prices) (Realization signature) Unit Unit where
  unitName := `ActualOptimizerPrimeLoss.firstLayer
  realizationName := `Reg.D5.S3.Arith.GoldenResource.ActualOptimizerPrimeLoss.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end
end Reg.D5.S3.Arith.GoldenResource.ActualOptimizerPrimeLoss
