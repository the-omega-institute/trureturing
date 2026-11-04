import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff
import Reg.Support.DependentFamily

/-! Source-bound audit of the normalized nonlocality–contextuality trade-off. -/

namespace Reg.D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff

open _root_.D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset
open _root_.D5.S3.Estimation.DecisionRisk.DescentDefectBounds
  (IsRowStochastic deterministicPostprocess)

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the affine Bell value at the stated behavior. -/
abbrev signature : Signature where
  Params := Σ n : ℕ, (Behavior n →ₗ[ℝ] ℝ) × ℝ
  State q := Behavior q.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q p => q.2.1 p + q.2.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n, 3 ≤ n → ∀ (f : (Behavior n →ₗ[ℝ] ℝ) × ℝ)
    (t : (BobBehavior n →ₗ[ℝ] ℝ) × ℝ),
    IsNormalizedGBell f → IsNormalizedNC t →
    ∀ p, IsNSND p → R.readout () ⟨n, f⟩ p + (t.1 (bobMarginal p) + t.2) ≤ 1

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
    norm_num [antiCount, deterministic, deterministicPostprocess, Prod.mk.injEq,
      Fin.sum_univ_succ, finRotate_apply, h₀, h₁, h₂]

private theorem triangle_normalized : IsNormalizedNC (antiCount, -2) := by
  refine ⟨?_, ?_, triangle, triangle_nsnd, ?_⟩
  · intro r hr
    have hsub : Set.range (deterministic : (Fin 3 → Bool) → BobBehavior 3) ⊆
        {r | antiCount r ≤ 2} := by
      rintro _ ⟨s, rfl⟩
      exact antiCount_deterministic s
    have hconv : Convex ℝ {r | antiCount r ≤ 2} :=
      (convex_Iic (2 : ℝ)).linear_preimage antiCount
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

private def evenScore (p : Behavior 3) (x : Fin 2) (i : Fin 3) : ℝ :=
  p x i false false false + p x i false true true +
    p x i true false true + p x i true true false

private def oddScore (p : Behavior 3) (x : Fin 2) (i : Fin 3) : ℝ :=
  p x i false false true + p x i false true false +
    p x i true false false + p x i true true true

private def wins : Behavior 3 →ₗ[ℝ] ℝ where
  toFun p := evenScore p 0 0 + evenScore p 0 1 + evenScore p 1 0 + oddScore p 1 1
  map_add' p q := by simp [evenScore, oddScore]; ring
  map_smul' a p := by simp [evenScore, oddScore]; ring

/-- A parity box with uniform Alice and single-measurement Bob marginals. -/
private def parityBox : Behavior 3 :=
  fun x i a b c =>
    if Bool.xor a (Bool.xor b c) = (decide (x = 1) && decide (i = 1)) then 1 / 4 else 0

private theorem parityBox_nsnd : IsNSND parityBox := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x i a b c
    dsimp only [parityBox]
    split_ifs <;> norm_num
  · intro x i
    simp only [Fintype.sum_bool]
    dsimp only [parityBox]
    cases h : (decide (x = 1) && decide (i = 1)) <;> norm_num
  · intro x i a c
    simp only [Fintype.sum_bool]
    dsimp only [parityBox]
    cases h : (decide (x = 1) && decide (i = 1)) <;>
      cases k : (decide (x = 1) && decide (finRotate 3 i = 1)) <;>
      cases a <;> cases c <;> norm_num
  · intro x y i b c
    simp only [Fintype.sum_bool]
    dsimp only [parityBox]
    cases h : (decide (x = 1) && decide (i = 1)) <;>
      cases k : (decide (y = 1) && decide (i = 1)) <;>
      cases b <;> cases c <;> norm_num
  · intro x i j a
    simp only [Fintype.sum_bool]
    dsimp only [parityBox]
    cases h : (decide (x = 1) && decide (i = 1)) <;>
      cases k : (decide (x = 1) && decide (j = 1)) <;> cases a <;> norm_num

private theorem wins_product (α : AliceResponse) (r : BobBehavior 3)
    (hα : IsRowStochastic α) (hr : IsND r) : wins (productBehavior α r) ≤ 3 := by
  have ha₀ := hα.2 0
  have ha₁ := hα.2 1
  have hr₀ := hr.2.1 0
  have hr₁ := hr.2.1 1
  simp only [Fintype.sum_bool] at ha₀ ha₁ hr₀ hr₁
  have hat₀ : α 0 true = 1 - α 0 false := by linarith
  have hat₁ : α 1 true = 1 - α 1 false := by linarith
  have hrt₀ : r 0 true true = 1 - r 0 false false - r 0 false true - r 0 true false := by
    linarith
  have hrt₁ : r 1 true true = 1 - r 1 false false - r 1 false true - r 1 true false := by
    linarith
  have he₀ := add_nonneg (hr.1 0 false false) (hr.1 0 true true)
  have he₁ := add_nonneg (hr.1 1 false false) (hr.1 1 true true)
  have ho₀ := add_nonneg (hr.1 0 false true) (hr.1 0 true false)
  have ho₁ := add_nonneg (hr.1 1 false true) (hr.1 1 true false)
  have hpos := add_nonneg
    (add_nonneg (mul_nonneg (mul_nonneg (hα.1 0 false) ho₀) ho₁)
      (mul_nonneg (mul_nonneg (hα.1 0 true) he₀) he₁))
    (add_nonneg (mul_nonneg (mul_nonneg (hα.1 1 false) ho₀) he₁)
      (mul_nonneg (mul_nonneg (hα.1 1 true) he₀) ho₁))
  change evenScore (productBehavior α r) 0 0 + evenScore (productBehavior α r) 0 1 +
    evenScore (productBehavior α r) 1 0 + oddScore (productBehavior α r) 1 1 ≤ 3
  dsimp only [evenScore, oddScore, productBehavior]
  rw [hat₀, hat₁, hrt₀, hrt₁] at hpos ⊢
  nlinarith only [hpos]

private theorem evenScore_bound {p : Behavior 3} (hp : IsNSND p) (x : Fin 2) (i : Fin 3) :
    evenScore p x i ≤ 1 := by
  have hn := hp.2.1 x i
  simp only [Fintype.sum_bool] at hn
  dsimp only [evenScore]
  linarith [hp.1 x i false false true, hp.1 x i false true false,
    hp.1 x i true false false, hp.1 x i true true true]

private theorem oddScore_bound {p : Behavior 3} (hp : IsNSND p) (x : Fin 2) (i : Fin 3) :
    oddScore p x i ≤ 1 := by
  have hn := hp.2.1 x i
  simp only [Fintype.sum_bool] at hn
  dsimp only [oddScore]
  linarith [hp.1 x i false false false, hp.1 x i false true true,
    hp.1 x i true false true, hp.1 x i true true false]

private theorem wins_normalized : IsNormalizedGBell (wins, -3) := by
  refine ⟨?_, ?_, parityBox, parityBox_nsnd, ?_⟩
  · intro p hp
    have hsub : {q : Behavior 3 | ∃ α r, IsRowStochastic α ∧ IsND r ∧
        q = productBehavior α r} ⊆ {q | wins q ≤ 3} := by
      rintro q ⟨α, r, hα, hr, rfl⟩
      exact wins_product α r hα hr
    have hconv : Convex ℝ {q : Behavior 3 | wins q ≤ 3} :=
      (convex_Iic (3 : ℝ)).linear_preimage wins
    have hb := convexHull_min hsub hconv hp
    change wins p ≤ 3 at hb
    change wins p + -3 ≤ 0
    linarith
  · intro p hp
    change evenScore p 0 0 + evenScore p 0 1 + evenScore p 1 0 + oddScore p 1 1 + -3 ≤ 1
    linarith [evenScore_bound hp 0 0, evenScore_bound hp 0 1,
      evenScore_bound hp 1 0, oddScore_bound hp 1 1]
  · norm_num [wins, evenScore, oddScore, parityBox]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 3 (by norm_num) (wins, -3) (antiCount, -2) wins_normalized triangle_normalized
    triangle triangle_nsnd
  norm_num [rejected, realize, antiCount, bobMarginal, triangle, Fintype.sum_bool] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  let probe : Behavior 3 →ₗ[ℝ] ℝ := {
    toFun := fun p => p 0 0 false false false
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  refine ⟨⟨3, probe, 0⟩, (fun _ _ _ _ _ => 0), (fun _ _ _ _ _ => 1), ?_⟩
  norm_num [actual, realize, probe]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
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
    (fun _ q p => q.2.1 p + q.2.2) (fun e => nomatch e))
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
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
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
