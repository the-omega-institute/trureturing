/- GID: D5/S3/Estimation/DataProcessing/IidStrictPeakSource
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/IidStrictPeakSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent finite ordered samples induce five legal peak modes and exact valley moments. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Estimation.DataProcessing.IidStrictPeakSource
open scoped BigOperators
noncomputable section
local instance propDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {A : Type*} [Fintype A] [LinearOrder A]

/-- Expectation under one draw, with the mass specified independently of any event. -/
def average (p : A → ℝ) (f : A → ℝ) : ℝ := ∑ a, p a * f a

/-- Five independent draws, in their original spatial order. -/
def productAverage (p : A → ℝ) (f : A → A → A → A → A → ℝ) : ℝ :=
  average p fun a => average p fun b => average p fun c =>
    average p fun d => average p fun e => f a b c d e

/-- A strict local maximum; ties do not count. -/
def peak (a b c : A) : Prop := a < b ∧ c < b

/-- The five mutually exclusive patterns: null, low, high, both ends, middle. -/
def mode (a b c d e : A) : Fin 5 :=
  if peak b c d then 4 else
  if peak a b c then (if peak c d e then 3 else 1) else
  if peak c d e then 2 else 0

/-- Pushforward of the independently specified product law by the peak classifier. -/
def modeLaw (p : A → ℝ) (s : Fin 5) : ℝ :=
  productAverage p fun a b c d e => if mode a b c d e = s then 1 else 0

/-- Probability of falling strictly below a letter. -/
def lowerMass (p : A → ℝ) (b : A) : ℝ := ∑ a, if a < b then p a else 0

/-- Probability that a two-letter wing has its tip strictly above the valley. -/
def wingMass (p : A → ℝ) (c : A) : ℝ :=
  ∑ b, if c < b then p b * lowerMass p b else 0

private theorem avg_const (p : A → ℝ) (hp : ∑ a, p a = 1) (c : ℝ) :
    average p (fun _ => c) = c := by simp [average, ← Finset.sum_mul, hp]

private theorem avg_add (p : A → ℝ) (f g : A → ℝ) :
    average p (fun a => f a + g a) = average p f + average p g := by
  simp [average, mul_add, Finset.sum_add_distrib]

private theorem avg_scale (p : A → ℝ) (c : ℝ) (f : A → ℝ) :
    average p (fun a => c * f a) = c * average p f := by
  simp [average, ← Finset.mul_sum, mul_left_comm]

private theorem avg_swap (p : A → ℝ) (f : A → A → ℝ) :
    average p (fun a => average p (f a)) =
      average p (fun b => average p (fun a => f a b)) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext b
  congr 1
  funext a
  ring

private theorem avg_right (p : A → ℝ) (c : ℝ) (f : A → ℝ) :
    average p (fun a => f a * c) = average p f * c := by
  simpa only [mul_comm] using avg_scale p c f

private theorem avg_rotate (p : A → ℝ) (f : A → A → A → ℝ) :
    average p (fun a => average p (fun b => average p (f a b))) =
      average p (fun c => average p (fun a => average p (fun b => f a b c))) := by
  simp_rw [avg_swap p (fun b c => f _ b c)]
  rw [avg_swap]

private theorem avg_nonneg (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) : 0 ≤ average p f :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hp a) (hf a)

private theorem peak_average (p : A → ℝ) :
    average p (fun a => average p (fun b => average p fun c =>
      if peak a b c then 1 else 0)) = ∑ b, p b * lowerMass p b ^ 2 := by
  classical
  rw [avg_swap]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  have inner (a : A) :
      average p (fun c => if peak a b c then (1 : ℝ) else 0) =
        (if a < b then lowerMass p b else 0) := by
    by_cases h : a < b
    · simp [average, peak, h, lowerMass]
    · simp [average, peak, h]
  simp only [inner, average]
  simp_rw [mul_ite, mul_zero]
  rw [show (∑ a, if a < b then p a * lowerMass p b else 0) =
      (∑ a, if a < b then p a else 0) * lowerMass p b by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _; split_ifs <;> simp]
  simp [lowerMass, pow_two]

private theorem wing_average (p : A → ℝ) (c : A) :
    average p (fun a => average p fun b => if peak a b c then (1 : ℝ) else 0) =
      wingMass p c := by
  classical
  rw [avg_swap]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : c < b
  · simp [average, peak, h, lowerMass, wingMass]
  · simp [average, peak, h, wingMass]

/-- Exact source bridge, including normalization, strict-peak exclusion,
three identical marginals and the second valley moment for the joint event. -/
theorem iid_peak_source (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    (∀ a b c d e : A, ¬ (peak a b c ∧ peak b c d) ∧
      ¬ (peak c d e ∧ peak b c d)) ∧
    (∀ s, 0 ≤ modeLaw p s) ∧ (∑ s, modeLaw p s) = 1 ∧
    modeLaw p 1 + modeLaw p 3 = ∑ b, p b * lowerMass p b ^ 2 ∧
    modeLaw p 2 + modeLaw p 3 = ∑ b, p b * lowerMass p b ^ 2 ∧
    modeLaw p 4 = ∑ b, p b * lowerMass p b ^ 2 ∧
    modeLaw p 3 = ∑ c, p c * wingMass p c ^ 2 ∧
    (∑ c, p c * wingMass p c) = ∑ b, p b * lowerMass p b ^ 2 ∧
    modeLaw p 0 * modeLaw p 3 - modeLaw p 1 * modeLaw p 2 =
      (1 - ∑ b, p b * lowerMass p b ^ 2) *
        (∑ c, p c * wingMass p c ^ 2) - (∑ b, p b * lowerMass p b ^ 2)^2 := by
  classical
  have excl (a b c d e : A) : ¬ (peak a b c ∧ peak b c d) ∧
      ¬ (peak c d e ∧ peak b c d) := by
    unfold peak
    constructor <;> rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
    · exact (lt_asymm h2 h3)
    · exact (lt_asymm h1 h4)
  have codes (a b c d e : A) :
      ((if mode a b c d e = 1 then (1 : ℝ) else 0) +
        (if mode a b c d e = 3 then 1 else 0) = if peak a b c then 1 else 0) ∧
      ((if mode a b c d e = 2 then (1 : ℝ) else 0) +
        (if mode a b c d e = 3 then 1 else 0) = if peak c d e then 1 else 0) ∧
      ((if mode a b c d e = 4 then (1 : ℝ) else 0) = if peak b c d then 1 else 0) ∧
      ((if mode a b c d e = 3 then (1 : ℝ) else 0) =
        (if peak a b c then 1 else 0) * (if peak c d e then 1 else 0)) := by
    have he := excl a b c d e
    by_cases hz : peak b c d <;> by_cases hx : peak a b c <;>
      by_cases hy : peak c d e <;> simp_all [mode]
  have lin (f g : A → A → A → A → A → ℝ) :
      productAverage p (fun a b c d e => f a b c d e + g a b c d e) =
        productAverage p f + productAverage p g := by
    simp only [productAverage, avg_add]
  have hmass : ∑ s, modeLaw p s = 1 := by
    rw [Fin.sum_univ_five]
    unfold modeLaw
    rw [← lin, ← lin, ← lin, ← lin]
    have hpoint (a b c d e : A) :
        (if mode a b c d e = 0 then (1 : ℝ) else 0) +
        (if mode a b c d e = 1 then 1 else 0) +
        (if mode a b c d e = 2 then 1 else 0) +
        (if mode a b c d e = 3 then 1 else 0) +
        (if mode a b c d e = 4 then 1 else 0) = 1 := by
      generalize mode a b c d e = s
      fin_cases s <;> norm_num
    simp only [hpoint, productAverage, avg_const p hs]
  have hx : modeLaw p 1 + modeLaw p 3 = ∑ b, p b * lowerMass p b ^ 2 := by
    unfold modeLaw
    rw [← lin]
    simp only [(codes _ _ _ _ _).1, productAverage, avg_const p hs]
    exact peak_average p
  have hy : modeLaw p 2 + modeLaw p 3 = ∑ b, p b * lowerMass p b ^ 2 := by
    unfold modeLaw
    rw [← lin]
    simp only [(codes _ _ _ _ _).2.1, productAverage]
    rw [peak_average p]
    simp only [avg_const p hs]
  have hz : modeLaw p 4 = ∑ b, p b * lowerMass p b ^ 2 := by
    simp only [modeLaw, (codes _ _ _ _ _).2.2.1, productAverage, avg_const p hs]
    rw [peak_average p]
    exact avg_const p hs _
  have hj : modeLaw p 3 = ∑ c, p c * wingMass p c ^ 2 := by
    simp only [modeLaw, (codes _ _ _ _ _).2.2.2, productAverage]
    rw [avg_rotate]
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    simp_rw [avg_scale]
    have hr : average p (fun d => average p fun e =>
        if peak c d e then (1 : ℝ) else 0) = wingMass p c := by
      rw [avg_swap]
      simpa only [peak, and_comm] using wing_average p c
    rw [hr]
    simp_rw [avg_right]
    rw [wing_average]
    ring
  have hm : (∑ c, p c * wingMass p c) = ∑ b, p b * lowerMass p b ^ 2 := by
    rw [← peak_average p]
    change average p (wingMass p) = _
    simp_rw [← wing_average]
    rw [avg_swap]
    congr 1
    funext a
    rw [avg_swap]
  refine ⟨excl, ?_, hmass, hx, hy, hz, hj, hm, ?_⟩
  · intro s
    unfold modeLaw productAverage
    repeat' apply avg_nonneg p hp
    intro e
    split_ifs <;> norm_num
  · rw [Fin.sum_univ_five] at hmass
    rw [← hx, ← hj]
    nlinarith [hmass, hy, hz]

#print axioms iid_peak_source
end
end D5.S3.Estimation.DataProcessing.IidStrictPeakSource
