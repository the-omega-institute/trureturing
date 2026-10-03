/- GID: D5/S3/Arith/FibonacciAtomic/WholeWindowJointIdentification
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/WholeWindowJointIdentification
   mirror-E: none(waiver:exact-finite-joint-law)
   anchors: []
   utility: none
   digest: Full joint laws identify the intensity and every increasing whole-window teacher. -/

import D5.S3.Arith.FibonacciAtomic.GarbledPosteriorRootGap
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FibonacciAtomic.WholeWindowJointIdentification

open LiteralWindowEnd
open scoped BigOperators

/-- Rows and columns use the fixed labels 0, 1, 2. -/
def channel : Fin 3 → Fin 3 → ℝ := ![
  ![1 / 2, Real.sqrt 2 - 1, (3 - 2 * Real.sqrt 2) / 2],
  ![1 / 4, 1 / 2, 1 / 4],
  ![(3 - 2 * Real.sqrt 2) / 2, Real.sqrt 2 - 1, 1 / 2]]

/-- The complete product domain retains every whole window. The selected
windows are passed directly to the ordered-priority teacher. -/
def jointMass {n : ℕ} (μ : Window → ℝ) (θ : Fin 3 → Fin n) (α : ℝ)
    (x : Fin n → Window) (j : Fin 3) : ℝ :=
  (∏ i, μ (x i)) *
    (α * channel (GarbledPosteriorRootGap.teacher (m := 0) (fun k => x (θ k))) j +
      (1 - α) / 3)

/-- Both arrays are strictly positive probability masses. Their full joint
laws agree exactly when their intensities agree and either that intensity
vanishes or their increasing triples agree. -/
theorem result (n : ℕ) (_hn : 3 ≤ n) (μ : Window → ℝ)
    (hμ : ∀ w, 0 < μ w) (hμsum : ∑ w, μ w = 1)
    (θ η : Fin 3 → Fin n) (hθ : StrictMono θ) (hη : StrictMono η)
    (α β : ℝ) (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) :
    ((∀ x j, 0 < jointMass μ θ α x j) ∧
      (∑ x : Fin n → Window, ∑ j : Fin 3, jointMass μ θ α x j) = 1) ∧
    ((∀ x j, 0 < jointMass μ η β x j) ∧
      (∑ x : Fin n → Window, ∑ j : Fin 3, jointMass μ η β x j) = 1) ∧
    (jointMass μ θ α = jointMass μ η β ↔ α = β ∧ (α = 0 ∨ θ = η)) := by
  classical
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by nlinarith
  have hs3 : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hQpos (c j : Fin 3) : 0 < channel c j := by
    fin_cases c <;> fin_cases j <;> norm_num [channel] <;> linarith
  have hQsum (c : Fin 3) : ∑ j, channel c j = 1 := by
    fin_cases c <;> simp [channel, Fin.sum_univ_succ] <;> ring
  have hinput (x : Fin n → Window) : 0 < ∏ i, μ (x i) :=
    Finset.prod_pos (fun i _ => hμ (x i))
  have hinputsum : (∑ x : Fin n → Window, ∏ i, μ (x i)) = 1 := by
    rw [← Fintype.prod_sum]
    simp [hμsum]
  have hlaw (τ : Fin 3 → Fin n) (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) :
      (∀ x j, 0 < jointMass μ τ a x j) ∧
        (∑ x : Fin n → Window, ∑ j : Fin 3, jointMass μ τ a x j) = 1 := by
    have hrow (c : Fin 3) : ∑ j : Fin 3, (a * channel c j + (1 - a) / 3) = 1 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hQsum]
      simp
      ring
    constructor
    · intro x j
      apply mul_pos (hinput x)
      change 0 < a * channel _ j + (1 - a) / 3
      by_cases ha0 : a = 0
      · simp [ha0]
      · exact add_pos_of_pos_of_nonneg
          (mul_pos (lt_of_le_of_ne ha.1 (Ne.symm ha0)) (hQpos _ j))
          (div_nonneg (sub_nonneg.mpr ha.2) (by norm_num))
    · simp only [jointMass, ← Finset.mul_sum, hrow, mul_one]
      exact hinputsum
  refine ⟨hlaw θ α hα, hlaw η β hβ, ?_⟩
  constructor
  · intro heq
    have hrows (x : Fin n → Window) (j : Fin 3) :
        α * channel (GarbledPosteriorRootGap.teacher (m := 0) (fun k => x (θ k))) j +
          (1 - α) / 3 =
        β * channel (GarbledPosteriorRootGap.teacher (m := 0) (fun k => x (η k))) j +
          (1 - β) / 3 :=
      mul_left_cancel₀ (hinput x).ne' (congrFun (congrFun heq x) j)
    have hab : α = β := by
      have hz := hrows (fun _ => Window.zero) 0
      norm_num [GarbledPosteriorRootGap.teacher, first, last, channel] at hz
      linarith
    refine ⟨hab, ?_⟩
    by_cases ha0 : α = 0
    · exact Or.inl ha0
    right
    have hQinj : Function.Injective (fun c : Fin 3 => channel c 0) := by
      intro c d h
      fin_cases c <;> fin_cases d
      all_goals first | rfl | (norm_num [channel] at h <;> nlinarith)
    have hteacher (x : Fin n → Window) :
        GarbledPosteriorRootGap.teacher (m := 0) (fun k => x (θ k)) =
          GarbledPosteriorRootGap.teacher (m := 0) (fun k => x (η k)) := by
      apply hQinj
      apply mul_left_cancel₀ ha0
      have h := hrows x 0
      rw [← hab] at h
      linarith
    let probe (a b : Fin n) : Fin n → Window :=
      fun i => if i = a then .high else if i = b then .low else .zero
    have hhigh (a b : Fin n) (i : Fin n) :
        last (probe a b i) = decide (i = a) := by
      by_cases hia : i = a
      · simp [probe, hia, last]
      · by_cases hib : i = b
        · subst i
          simp [probe, hia, last]
        · simp [probe, hia, hib, last]
    have hlow (a b : Fin n) (hab : a ≠ b) (i : Fin n) :
        first (probe a b i) = decide (i = b) := by
      by_cases hia : i = a
      · subst i
        simp [probe, hab, first]
      · by_cases hib : i = b
        · subst i
          simp [probe, hia, first]
        · simp [probe, hia, hib, first]
    have hrole1 (a b : Fin n) (hab : a ≠ b) (τ : Fin 3 → Fin n)
        (hout : GarbledPosteriorRootGap.teacher (m := 0)
          (fun k => probe a b (τ k)) = 1) : τ 0 = a ∧ τ 1 = b := by
      simp only [GarbledPosteriorRootGap.teacher, hhigh, hlow a b hab] at hout
      split_ifs at hout with h1 h2
      · simpa using h1
      · have := congrArg Fin.val hout
        norm_num at this
      · have := congrArg Fin.val hout
        norm_num at this
    have hrole2 (a b : Fin n) (hab : a ≠ b) (τ : Fin 3 → Fin n)
        (hout : GarbledPosteriorRootGap.teacher (m := 0)
          (fun k => probe a b (τ k)) = 2) : τ 1 = a ∧ τ 2 = b := by
      simp only [GarbledPosteriorRootGap.teacher, hhigh, hlow a b hab] at hout
      split_ifs at hout with h1 h2
      · have := congrArg Fin.val hout
        norm_num at this
      · simpa using h2
      · have := congrArg Fin.val hout
        norm_num at this
    have ht01 : θ 0 ≠ θ 1 := ne_of_lt (hθ (by decide : (0 : Fin 3) < 1))
    have ht12 : θ 1 ≠ θ 2 := ne_of_lt (hθ (by decide : (1 : Fin 3) < 2))
    have hout1 : GarbledPosteriorRootGap.teacher (m := 0)
        (fun k => probe (θ 0) (θ 1) (θ k)) = 1 := by
      simp [GarbledPosteriorRootGap.teacher, hhigh, hlow _ _ ht01]
    have hout2 : GarbledPosteriorRootGap.teacher (m := 0)
        (fun k => probe (θ 1) (θ 2) (θ k)) = 2 := by
      simp [GarbledPosteriorRootGap.teacher, hhigh, hlow _ _ ht12, ht01]
    have hpq := hrole1 (θ 0) (θ 1) ht01 η
      ((hteacher (probe (θ 0) (θ 1))).symm.trans hout1)
    have hqr := hrole2 (θ 1) (θ 2) ht12 η
      ((hteacher (probe (θ 1) (θ 2))).symm.trans hout2)
    funext k
    fin_cases k
    · exact hpq.1.symm
    · exact hpq.2.symm
    · exact hqr.2.symm
  · rintro ⟨hab, ha0 | hθη⟩
    · subst β
      funext x j
      simp [jointMass, ha0]
    · subst η
      subst β
      rfl

end D5.S3.Arith.FibonacciAtomic.WholeWindowJointIdentification
