import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.GoldenResource.GoldenResourceLargestOptimizer
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenResource.GoldenResourceLargestOptimizer

open Finset
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceLargestOptimizer
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace Spec

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {lambda : ℝ}, 0 < lambda →
    1 ≤ r.readout () () lambda ∧
    (∀ p : ℕ, (largestCA lambda).factorization p = fullCALayerCount lambda p) ∧
    (∀ p : ℕ, ¬p.Prime → fullCALayerCount lambda p = 0) ∧
    (∀ p k : ℕ, p.Prime →
      (1 ≤ k ∧ k ≤ (largestCA lambda).factorization p ↔
        1 ≤ k ∧ lambda ≤ goldenLayerMarginal p k)) ∧
    IsGoldenResourceOptimal lambda (largestCA lambda) ∧
    ∀ m : ℕ, 1 ≤ m → IsGoldenResourceOptimal lambda m → m ∣ largestCA lambda

def actual : Realization signature :=
  realize signature (fun _ _ lambda => largestCA lambda) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : 1 ≤ (0 : ℕ) := (h (lambda := 1) (by norm_num)).1
  omega

def family : Registration arena (type_of% @largest_ca_spec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨largest_ca_spec, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), -1, (1 / 25 : ℝ), ?_⟩
    change largestCA (-1) ≠ largestCA (1 / 25)
    have hs := largest_ca_spec (lambda := (1 / 25 : ℝ)) (by norm_num)
    have hle := hs.2.2.2.2.1 5040 (by norm_num)
    have hu := golden_resource_unique_optimum hs.1
    have heq : largestCA (1 / 25) = 5040 := hu.2.mp (le_antisymm hu.1 hle)
    rw [heq]
    norm_num [largestCA, fullCALayers]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@largest_ca_spec)
    (type_of% (realize signature actual.readout actual.anchor))
    Unit Unit where
  unitName := `D5.S3.Arith.GoldenResource.GoldenResourceLargestOptimizer.largest_ca_spec.__information_unit
  realizationName := `Reg.D5.S3.Arith.GoldenResource.GoldenResourceLargestOptimizer.Spec.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.GoldenResource.GoldenResourceLargestOptimizer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Spec

namespace Clock

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {lambda1 lambda2 : ℝ}, 0 < lambda2 → lambda2 < lambda1 →
    largestCA lambda1 ∣ largestCA lambda2 ∧
    r.readout () () (largestCA lambda2 : ℝ) - Real.log (largestCA lambda1 : ℝ) =
      ∑ pk ∈ (fullCALayers lambda2).filter
        (fun pk => goldenLayerMarginal pk.1 pk.2 < lambda1), Real.log (pk.1 : ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => Real.log x + 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h (lambda1 := 2) (lambda2 := 1) (by norm_num) (by norm_num)).2
  have hgood := (largest_ca_clock (lambda1 := 2) (lambda2 := 1)
    (by norm_num) (by norm_num)).2
  change Real.log (largestCA 1 : ℝ) + 1 - Real.log (largestCA 2 : ℝ) = _ at hbad
  linarith

def family : Registration arena (type_of% @largest_ca_clock) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨largest_ca_clock, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change Real.log 1 ≠ Real.log 2
    rw [Real.log_one]
    exact (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))).symm

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@largest_ca_clock)
    (type_of% (realize signature actual.readout actual.anchor))
    Unit Unit where
  unitName := `D5.S3.Arith.GoldenResource.GoldenResourceLargestOptimizer.largest_ca_clock.__information_unit
  realizationName := `Reg.D5.S3.Arith.GoldenResource.GoldenResourceLargestOptimizer.Clock.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.GoldenResource.GoldenResourceLargestOptimizer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Clock

#print axioms Spec.registration
#print axioms Clock.registration

end
end Reg.D5.S3.Arith.GoldenResource.GoldenResourceLargestOptimizer
