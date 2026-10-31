import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff
import Reg.Support.DependentFamily

/-! Source-bound audit of the normalized nonlocality–contextuality trade-off. -/

namespace Reg.D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff

open _root_.D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Evaluate the source normalization predicate at the stated affine functional. -/
abbrev signature : Signature where
  Params := Σ n : ℕ, (Behavior n →ₗ[ℝ] ℝ) × ℝ
  State q := ((Behavior q.1 →ₗ[ℝ] ℝ) × ℝ) → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q H => @decide (H q.2) (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n, 3 ≤ n → ∀ (f : (Behavior n →ₗ[ℝ] ℝ) × ℝ)
    (t : (BobBehavior n →ₗ[ℝ] ℝ) × ℝ),
    R.readout () ⟨n, f⟩ IsNormalizedGBell = true → IsNormalizedNC t →
    ∀ p, IsNSND p → f.1 p + f.2 + (t.1 (bobMarginal p) + t.2) ≤ 1

/-- The number of anticorrelated edges in the three-cycle. -/
private def antiCount : BobBehavior 3 →ₗ[ℝ] ℝ where
  toFun r := ∑ i, (r i false true + r i true false)
  map_add' r s := by simp [sum_add_distrib]; ring
  map_smul' a r := by simp [mul_add, mul_sum]

private def triangle : Behavior 3 :=
  fun _ _ _ b c => if b ≠ c then 1 / 4 else 0

private theorem triangle_nsnd : IsNSND triangle := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x i a b c
    dsimp [triangle]
    split_ifs <;> norm_num
  · intro x i
    simp only [Fintype.sum_bool]
    norm_num [triangle]
  · intro x i a c
    simp only [Fintype.sum_bool]
    cases c <;> norm_num [triangle]
  · intro x y i b c
    rfl
  · intro x i j a
    rfl

private theorem antiCount_deterministic (s : Fin 3 → Bool) :
    antiCount (deterministic s) ≤ 2 := by
  cases h₀ : s 0 <;> cases h₁ : s 1 <;> cases h₂ : s 2 <;>
    norm_num [antiCount, deterministic, Fin.sum_univ_succ, finRotate_apply, h₀, h₁, h₂]

private theorem triangle_normalized : IsNormalizedNC (antiCount, -2) := by
  refine ⟨?_, ?_, triangle, triangle_nsnd, ?_⟩
  · intro r hr
    have hsub : Set.range (deterministic : (Fin 3 → Bool) → BobBehavior 3) ⊆
        {r | antiCount r ≤ 2} := by
      rintro _ ⟨s, rfl⟩
      exact antiCount_deterministic s
    have hconv : Convex ℝ {r | antiCount r ≤ 2} := by
      intro r hr s hs a b ha hb hab
      change antiCount (a • r + b • s) ≤ 2
      rw [map_add, map_smul, map_smul]
      change a * antiCount r + b * antiCount s ≤ 2
      calc
        _ ≤ a * 2 + b * 2 := add_le_add (mul_le_mul_of_nonneg_left hr ha)
          (mul_le_mul_of_nonneg_left hs hb)
        _ = 2 := by linarith [hab]
    have hbound := convexHull_min hsub hconv hr
    change antiCount r ≤ 2 at hbound
    change antiCount r + -2 ≤ 0
    linarith
  · intro p hp
    have heach (i : Fin 3) :
        bobMarginal p i false true + bobMarginal p i true false ≤ 1 := by
      have hnorm := hp.2.1 0 i
      have h₀ := hp.1 0 i false false false
      have h₁ := hp.1 0 i true false false
      have h₂ := hp.1 0 i false true true
      have h₃ := hp.1 0 i true true true
      simp only [Fintype.sum_bool] at hnorm
      simp only [bobMarginal, Fintype.sum_bool]
      linarith
    have hb := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 3))) => heach i)
    change antiCount (bobMarginal p) + -2 ≤ 1
    change (∑ i, (bobMarginal p i false true + bobMarginal p i true false)) ≤
      ∑ _ : Fin 3, (1 : ℝ) at hb
    norm_num at hb
    change (∑ i, (bobMarginal p i false true + bobMarginal p i true false)) + -2 ≤ 1
    linarith
  · norm_num [antiCount, bobMarginal, triangle, Fintype.sum_bool]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 3 (by norm_num) (0, 2) (antiCount, -2) rfl triangle_normalized
    triangle triangle_nsnd
  norm_num [antiCount, bobMarginal, triangle, Fintype.sum_bool] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨3, 0, 0⟩, (fun _ => True), (fun _ => False), ?_⟩
  simp [actual, realize]

def source_registration : Registration arena claim where
  actual := actual
  bridge := by simp [actual, realize, claim]
  variation := ⟨by simpa [actual, realize, arena, claim] using result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.unit
  realizationName :=
    `Reg.D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ q H => @decide (H q.2) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff
    definition := some {
      owner := `D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff
      name := `D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.claim
      path := #[] }
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.result
#print _root_.D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff
