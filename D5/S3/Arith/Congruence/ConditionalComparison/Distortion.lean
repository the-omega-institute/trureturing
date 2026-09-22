/- GID: D5/S3/Arith/Congruence/ConditionalComparison/Distortion
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Fibrewise distortion. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/Distortion.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.FiniteProbability
import Mathlib.Tactic

/-!
# Fibrewise distortion

This module formalizes the normalized one-fibre update.  The global sequential
distortion is obtained by applying this exact construction independently on
every fibre of the preceding history.
-/

namespace Erdos7

/-- Multiplier on the charged event. -/
def insideMultiplier (δ α : ℚ) : ℚ :=
  if α ≤ δ then 0 else (α - δ) / (α * (1 - δ))

/-- Multiplier on the complement of the charged event. -/
def outsideMultiplier (δ α : ℚ) : ℚ :=
  if α ≤ δ then (1 - α)⁻¹ else (1 - δ)⁻¹

/-- Mass retained by the charged event after distortion. -/
def thresholdMass (δ α : ℚ) : ℚ :=
  if α ≤ δ then 0 else (α - δ) / (1 - δ)

theorem distortion_average_one
    {δ α : ℚ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    α * insideMultiplier δ α + (1 - α) * outsideMultiplier δ α = 1 := by
  by_cases h : α ≤ δ
  · have hden : 1 - α ≠ 0 := by linarith
    simp [insideMultiplier, outsideMultiplier, h, hden]
  · have hαpos : 0 < α := by linarith
    have hδden : 1 - δ ≠ 0 := by linarith
    simp [insideMultiplier, outsideMultiplier, h]
    field_simp
    ring

theorem distortion_inside_mass
    {δ α : ℚ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hα0 : 0 ≤ α) :
    α * insideMultiplier δ α = thresholdMass δ α := by
  by_cases h : α ≤ δ
  · simp [insideMultiplier, thresholdMass, h]
  · have hαne : α ≠ 0 := by linarith
    have hδden : 1 - δ ≠ 0 := by linarith
    simp [insideMultiplier, thresholdMass, h]
    field_simp

theorem insideMultiplier_nonneg
    {δ α : ℚ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hα0 : 0 ≤ α) :
    0 ≤ insideMultiplier δ α := by
  by_cases h : α ≤ δ
  · simp [insideMultiplier, h]
  · have hαpos : 0 < α := by linarith
    have hden : 0 < α * (1 - δ) := mul_pos hαpos (by linarith)
    simp only [insideMultiplier, h, ↓reduceIte]
    exact div_nonneg (by linarith) hden.le

theorem outsideMultiplier_nonneg
    {δ α : ℚ} (hδ1 : δ < 1) (hα1 : α ≤ 1) :
    0 ≤ outsideMultiplier δ α := by
  by_cases h : α ≤ δ
  · simp only [outsideMultiplier, h, ↓reduceIte]
    exact inv_nonneg.mpr (by linarith)
  · simp only [outsideMultiplier, h, ↓reduceIte]
    exact inv_nonneg.mpr (by linarith)

/-- Every fibre multiplier is bounded by the reciprocal retained mass. -/
theorem insideMultiplier_le
    {δ α : ℚ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    insideMultiplier δ α ≤ (1 - δ)⁻¹ := by
  by_cases h : α ≤ δ
  · simp only [insideMultiplier, h, ↓reduceIte]
    exact inv_nonneg.mpr (by linarith)
  · have hαpos : 0 < α := by linarith
    have hden : 0 < 1 - δ := by linarith
    simp only [insideMultiplier, h, ↓reduceIte]
    rw [div_le_iff₀ (mul_pos hαpos hden)]
    have hcancel : (1 - δ)⁻¹ * (α * (1 - δ)) = α := by
      field_simp
    rw [hcancel]
    linarith

/-- The complementary fibre multiplier has the same sharp upper bound. -/
theorem outsideMultiplier_le
    {δ α : ℚ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    outsideMultiplier δ α ≤ (1 - δ)⁻¹ := by
  by_cases h : α ≤ δ
  · simp only [outsideMultiplier, h, ↓reduceIte]
    exact (inv_le_inv₀ (by linarith : 0 < 1 - α)
      (by linarith : 0 < 1 - δ)).2 (by linarith)
  · simp [outsideMultiplier, h]

/-- Pointwise form of the multiplier bound, convenient for kernels. -/
theorem distortionMultiplier_le
    {δ α : ℚ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (b : Bool) :
    (if b then insideMultiplier δ α else outsideMultiplier δ α) ≤
      (1 - δ)⁻¹ := by
  cases b
  · simpa using outsideMultiplier_le hδ0 hδ1 hα0 hα1
  · simpa using insideMultiplier_le hδ0 hδ1 hα0 hα1

/--
The scalar hinge estimate used at a digit stage.  If an event occupies at
most `m` of `q` equiprobable symbols, thresholding at `t/q` costs at most
`(m-t)₊/(q-t)`.
-/
theorem thresholdMass_le_cardHinge
    {α : ℚ} {q t m : ℕ} (hq : 0 < q) (ht : t < q)
    (hα0 : 0 ≤ α) (hα : α ≤ (m : ℚ) / q) :
    thresholdMass ((t : ℚ) / q) α ≤
      ((m - t : ℕ) : ℚ) / (q - t) := by
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have htQ : (t : ℚ) < q := by exact_mod_cast ht
  have hqt : (0 : ℚ) < (q : ℚ) - t := sub_pos.mpr htQ
  by_cases hmt : m ≤ t
  · have hmq : (m : ℚ) / q ≤ (t : ℚ) / q := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmt) hqQ.le
    have hαt : α ≤ (t : ℚ) / q := hα.trans hmq
    simp [thresholdMass, hαt, Nat.sub_eq_zero_of_le hmt]
  · have htm : t < m := Nat.lt_of_not_ge hmt
    by_cases hαt : α ≤ (t : ℚ) / q
    · simp [thresholdMass, hαt]
      positivity
    · simp only [thresholdMass, hαt, ↓reduceIte]
      have hden : (0 : ℚ) < 1 - (t : ℚ) / q := by
        rw [sub_pos]
        exact (div_lt_one hqQ).mpr (by exact_mod_cast ht)
      apply (div_le_div_iff₀ hden hqt).2
      have hmcast : ((m - t : ℕ) : ℚ) = (m : ℚ) - t := by
        rw [Nat.cast_sub htm.le]
      rw [hmcast]
      have hαmul := mul_le_mul_of_nonneg_right hα hqQ.le
      field_simp at hαmul ⊢
      nlinarith

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

/-- The normalized distortion of a finite rational law by one event. -/
noncomputable def distort (μ : FiniteLaw Ω) (A : Ω → Prop) [DecidablePred A]
    (δ : ℚ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : FiniteLaw Ω := by
  let α := μ.prob A
  have hα0 : 0 ≤ α := μ.prob_nonneg A
  have hα1 : α ≤ 1 := μ.prob_le_one A
  refine
    { weight := fun ω ↦ μ.weight ω *
        (if A ω then insideMultiplier δ α else outsideMultiplier δ α)
      weight_nonneg := ?_
      weight_sum := ?_ }
  · intro ω
    apply mul_nonneg (μ.weight_nonneg ω)
    by_cases hA : A ω
    · simp only [hA, ↓reduceIte]
      exact insideMultiplier_nonneg hδ0 hδ1 hα0
    · simp only [hA, ↓reduceIte]
      exact outsideMultiplier_nonneg hδ1 hα1
  · change μ.expect (fun ω ↦
      if A ω then insideMultiplier δ α else outsideMultiplier δ α) = 1
    rw [μ.expect_ite]
    exact distortion_average_one hδ0 hδ1 hα0 hα1

@[simp] theorem distort_weight (μ : FiniteLaw Ω) (A : Ω → Prop)
    [DecidablePred A] (δ : ℚ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (ω : Ω) :
    (μ.distort A δ hδ0 hδ1).weight ω = μ.weight ω *
      (if A ω then insideMultiplier δ (μ.prob A)
       else outsideMultiplier δ (μ.prob A)) := rfl

/-- Distortion enlarges no atom by more than `(1-δ)⁻¹`. -/
theorem distort_weight_le (μ : FiniteLaw Ω) (A : Ω → Prop)
    [DecidablePred A] (δ c : ℚ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (ω : Ω) (hω : μ.weight ω ≤ c) :
    (μ.distort A δ hδ0 hδ1).weight ω ≤ c * (1 - δ)⁻¹ := by
  let α := μ.prob A
  have hα0 : 0 ≤ α := μ.prob_nonneg A
  have hα1 : α ≤ 1 := μ.prob_le_one A
  let M := if A ω then insideMultiplier δ α else outsideMultiplier δ α
  have hM0 : 0 ≤ M := by
    by_cases hA : A ω
    · simp only [M, hA, ↓reduceIte]
      exact insideMultiplier_nonneg hδ0 hδ1 hα0
    · simp only [M, hA, ↓reduceIte]
      exact outsideMultiplier_nonneg hδ1 hα1
  have hM : M ≤ (1 - δ)⁻¹ := by
    by_cases hA : A ω
    · simp only [M, hA, ↓reduceIte]
      exact insideMultiplier_le hδ0 hδ1 hα0 hα1
    · simp only [M, hA, ↓reduceIte]
      exact outsideMultiplier_le hδ0 hδ1 hα0 hα1
  have hc : 0 ≤ c := (μ.weight_nonneg ω).trans hω
  change μ.weight ω * M ≤ c * (1 - δ)⁻¹
  exact mul_le_mul hω hM hM0 hc

/-- The digit cap obtained from a uniform `q`-ary atom bound. -/
theorem distort_uniform_atom_cap (μ : FiniteLaw Ω) (A : Ω → Prop)
    [DecidablePred A] {q t : ℕ} (hq : 0 < q) (ht : t < q)
    (hunif : ∀ ω, μ.weight ω ≤ (q : ℚ)⁻¹) (ω : Ω) :
    (μ.distort A ((t : ℚ) / q)
      (by positivity) (by
        have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
        exact (div_lt_one hqQ).mpr (by exact_mod_cast ht))).weight ω ≤
      ((q - t : ℕ) : ℚ)⁻¹ := by
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have htQ : (t : ℚ) < q := by exact_mod_cast ht
  have hδ1 : (t : ℚ) / q < 1 := (div_lt_one hqQ).mpr htQ
  have h := μ.distort_weight_le A ((t : ℚ) / q) (q : ℚ)⁻¹
    (by positivity) hδ1 ω (hunif ω)
  calc
    (μ.distort A ((t : ℚ) / q) (by positivity) hδ1).weight ω
        ≤ (q : ℚ)⁻¹ * (1 - (t : ℚ) / q)⁻¹ := h
    _ = ((q - t : ℕ) : ℚ)⁻¹ := by
      rw [Nat.cast_sub ht.le]
      field_simp

theorem distort_prob (μ : FiniteLaw Ω) (A : Ω → Prop) [DecidablePred A]
    (δ : ℚ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (μ.distort A δ hδ0 hδ1).prob A = thresholdMass δ (μ.prob A) := by
  let α := μ.prob A
  have hα0 : 0 ≤ α := μ.prob_nonneg A
  change (∑ ω, μ.weight ω *
      (if A ω then insideMultiplier δ α else outsideMultiplier δ α) *
      (if A ω then 1 else 0)) = thresholdMass δ α
  rw [← distortion_inside_mass hδ0 hδ1 hα0]
  rw [← μ.expect_indicator_mul A (insideMultiplier δ α)]
  unfold expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hA : A ω <;> simp [hA]

end FiniteLaw
end Erdos7
