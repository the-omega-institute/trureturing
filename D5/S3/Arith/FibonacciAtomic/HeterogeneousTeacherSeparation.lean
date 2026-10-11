/- GID: D5/S3/Arith/FibonacciAtomic/HeterogeneousTeacherSeparation
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/HeterogeneousTeacherSeparation
   mirror-E: none(waiver:unbounded-symbolic-estimate)
   anchors: []
   utility: none
   digest: Independent heterogeneous whole-window laws have a sharp uniform teacher separation. -/

import D5.S3.Arith.FibonacciAtomic.GarbledPosteriorRootGap
import D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FibonacciAtomic.HeterogeneousTeacherSeparation

open LiteralWindowEnd (Window first last)
open LegalPriorityTeacher (Input Roles)
open scoped BigOperators

/-- Real masses on the five actual windows at each position. No seam conditioning. -/
abbrev Laws (n : ℕ) := Fin n → Window → ℝ

/-- Every one of the five masses is at least rho and each position has total mass one. -/
def Admissible {n : ℕ} (rho : ℝ) (μ : Laws n) : Prop :=
  (∀ i a, rho ≤ μ i a) ∧ (∀ i, ∑ a, μ i a = 1)

/-- The frozen priority teacher on the three selected actual windows, as a real class value. -/
def classValue {n : ℕ} (t : Roles n) (w : Input n) : ℝ :=
  (GarbledPosteriorRootGap.teacher (m := 0) ![w t.p, w t.q, w t.r]).val

/-- Squared separation in the full heterogeneous product input law. -/
def distance {n : ℕ} (μ : Laws n) (t u : Roles n) : ℝ :=
  ∑ w : Input n, (∏ i, μ i (w i)) * (classValue t w - classValue u w) ^ 2

/-- The sharp constant for the entire admissible heterogeneous class. -/
def gamma (rho : ℝ) : ℝ := 8 * rho ^ 2 * (1 - 2 * rho)

/-- A common law attaining the heterogeneous infimum; order is zero, low, middle, ends, high. -/
def extremal (rho : ℝ) : Window → ℝ
  | .zero | .middle => (1 - 3 * rho) / 2
  | .low | .ends | .high => rho

/-- Product expectation in the actual heterogeneous input law. -/
def productExpectation {n : ℕ} (μ : Laws n) (f : Input n → ℝ) : ℝ :=
  ∑ w : Input n, (∏ i, μ i (w i)) * f w

/-- High endpoint indicator. -/
def highIndicator (a : Window) : ℝ := if last a then 1 else 0

/-- Low endpoint indicator. -/
def lowIndicator (a : Window) : ℝ := if first a then 1 else 0

/-- High endpoint marginal in one actual window. -/
def highMarginal {n : ℕ} (μ : Laws n) (i : Fin n) : ℝ := μ i .ends + μ i .high

/-- Low endpoint marginal in one actual window. -/
def lowMarginal {n : ℕ} (μ : Laws n) (i : Fin n) : ℝ := μ i .ends + μ i .low

/-- First priority gate. -/
def firstGate {n : ℕ} (t : Roles n) (w : Input n) : ℝ :=
  highIndicator (w t.p) * lowIndicator (w t.q)

variable {n : ℕ}

private theorem product_expectation_factorization {μ : Laws n} (hsum : ∀ i, ∑ a, μ i a = 1)
    (S : Finset (Fin n)) (f : Fin n → Window → ℝ) :
    productExpectation μ (fun w => ∏ i ∈ S, f i (w i)) = ∏ i ∈ S, ∑ a, μ i a * f i a := by
  classical
  have h := (Fintype.prod_sum (fun i a => μ i a *
    (if i ∈ S then f i a else 1))).symm
  have hl (w : Input n) :
      (∏ i, μ i (w i) * (if i ∈ S then f i (w i) else 1)) =
        (∏ i, μ i (w i)) * ∏ i ∈ S, f i (w i) := by
    rw [Finset.prod_mul_distrib]
    simp
  have hr (i : Fin n) :
      (∑ a, μ i a * (if i ∈ S then f i a else 1)) =
        if i ∈ S then ∑ a, μ i a * f i a else 1 := by
    by_cases hmem : i ∈ S <;> simp [hmem, hsum]
  simpa only [productExpectation, hl, hr, Finset.prod_ite_mem, Finset.univ_inter] using h

theorem product_expectation_two_positions {μ : Laws n} (hsum : ∀ i, ∑ a, μ i a = 1)
    (p q : Fin n) (hpq : p ≠ q) (f g : Window → ℝ) :
    productExpectation μ (fun w => f (w p) * g (w q)) =
      (∑ a, μ p a * f a) * (∑ a, μ q a * g a) := by
  classical
  simpa [hpq, Ne.symm hpq] using
    product_expectation_factorization hsum {p, q} (fun i a => if i = p then f a else g a)

theorem product_expectation_three_positions {μ : Laws n} (hsum : ∀ i, ∑ a, μ i a = 1)
    (p q r : Fin n) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (f g h : Window → ℝ) :
    productExpectation μ (fun w => f (w p) * g (w q) * h (w r)) =
      (∑ a, μ p a * f a) * (∑ a, μ q a * g a) * (∑ a, μ r a * h a) := by
  classical
  simpa [hpq, hpr, hqr, Ne.symm hpq, Ne.symm hpr, Ne.symm hqr, mul_assoc] using
    product_expectation_factorization hsum {p, q, r} (fun i a => if i = p then f a else if i = q
        then g a else h a)

theorem product_expectation_four_positions {μ : Laws n} (hsum : ∀ i, ∑ a, μ i a = 1)
    (p q r s : Fin n) (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) (f g h k : Window → ℝ) :
    productExpectation μ (fun w => f (w p) * g (w q) * h (w r) * k (w s)) =
      (∑ a, μ p a * f a) * (∑ a, μ q a * g a) *
        (∑ a, μ r a * h a) * (∑ a, μ s a * k a) := by
  classical
  simpa [hpq, hpr, hps, hqr, hqs, hrs, Ne.symm hpq, Ne.symm hpr,
    Ne.symm hps, Ne.symm hqr, Ne.symm hqs, Ne.symm hrs, mul_assoc] using
    product_expectation_factorization hsum {p, q, r, s} (fun i a => if i = p then f a else if i =
        q then g a
      else if i = r then h a else k a)

theorem product_expectation_linear_combination {μ : Laws n} (f g h : Input n → ℝ) (a b c : ℝ) :
    productExpectation μ (fun w => a * f w + b * g w + c * h w) = a * productExpectation μ f + b *
        productExpectation μ g + c * productExpectation μ h := by
  classical
  have scale (d : ℝ) (f : Input n → ℝ) : productExpectation μ (fun w => d * f w) = d *
      productExpectation μ f := by
    dsimp [productExpectation]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  calc
    _ = productExpectation μ (fun w => a * f w) + productExpectation μ (fun w => b * g w) +
        productExpectation μ (fun w => c * h w) := by simp [productExpectation, mul_add,
            Finset.sum_add_distrib]
    _ = _ := by rw [scale, scale, scale]

private theorem bernoulli_discrepancy_rectangle_lower (b c s t : ℝ) (hbc : b ≤ c)
    (hs : b ≤ s ∧ s ≤ c)
    (ht : b ≤ t ∧ t ≤ c) (hb : b ≤ 1 / 2) (hbc1 : b + c ≤ 1) :
    2 * b * (1 - b) ≤ s + t - 2 * s * t := by
  classical
  by_cases ht2 : t ≤ 1 / 2
  · have h1 := mul_nonneg (sub_nonneg.mpr hs.1)
      (show 0 ≤ 1 - 2 * t by linarith)
    have h2 := mul_nonneg (sub_nonneg.mpr ht.1)
      (show 0 ≤ 1 - 2 * b by linarith)
    nlinarith
  · have h1 := mul_nonneg (sub_nonneg.mpr hs.2)
      (show 0 ≤ 2 * t - 1 by linarith)
    have h2 := mul_nonneg (sub_nonneg.mpr ht.2)
      (show 0 ≤ 2 * c - 1 by linarith [ht.2])
    have h3 := mul_nonneg (sub_nonneg.mpr hbc)
      (show 0 ≤ 1 - c - b by linarith)
    nlinarith

theorem high_indicator_mean (μ : Laws n) (i : Fin n) : (∑ a, μ i a * highIndicator a) =
    highMarginal μ i := by
  classical
  simp [Finset.univ, Fintype.elems, highIndicator, last,
      highMarginal]

theorem low_indicator_mean (μ : Laws n) (i : Fin n) : (∑ a, μ i a * lowIndicator a) = lowMarginal
    μ i := by
  classical
  simp [Finset.univ, Fintype.elems, lowIndicator, first,
      lowMarginal, add_comm]

theorem joint_endpoint_mean (μ : Laws n) (i : Fin n) : (∑ a, μ i a * (lowIndicator a *
    highIndicator a)) = μ i .ends := by
  classical
  simp [Finset.univ, Fintype.elems, highIndicator,
      lowIndicator, first, last]

theorem endpoint_indicators_binary (a : Window) : (highIndicator a = 0 ∨ highIndicator a = 1) ∧
    (lowIndicator a = 0 ∨ lowIndicator a = 1) := by
  classical
  cases a <;> simp [highIndicator, lowIndicator, first, last]

theorem first_gate_binary (a b : Window) : highIndicator a * lowIndicator b = 0 ∨ highIndicator a
    * lowIndicator b = 1 := by
  classical
  rcases (endpoint_indicators_binary a).1 with ha | ha <;>
    rcases (endpoint_indicators_binary b).2 with hb | hb <;> simp [ha, hb]

theorem class_value_formula (t : Roles n) (w : Input n) :
    classValue t w = firstGate t w + 2 * (1 - firstGate t w) * (highIndicator (w t.q) *
        lowIndicator (w t.r)) := by
  classical
  cases hp : last (w t.p) <;> cases hq : first (w t.q) <;>
    cases hq' : last (w t.q) <;> cases hr' : first (w t.r) <;>
    norm_num [classValue, GarbledPosteriorRootGap.teacher, Matrix.cons_val_two,
      firstGate, highIndicator, lowIndicator, hp, hq, hq', hr']

private theorem first_gate_sq_le_class_sq (t u : Roles n) (w : Input n) :
    (firstGate t w - firstGate u w) ^ 2 ≤ (classValue t w - classValue u w) ^ 2 := by
  classical
  rw [class_value_formula, class_value_formula]
  rcases first_gate_binary (w t.p) (w t.q) with ht | ht <;>
    rcases first_gate_binary (w u.p) (w u.q) with hu | hu <;>
    rcases first_gate_binary (w t.q) (w t.r) with hb | hb <;>
    rcases first_gate_binary (w u.q) (w u.r) with hc | hc <;>
    norm_num [firstGate, ht, hu, hb, hc]

private theorem first_gate_sq_eq_discrepancy (t u : Roles n) (w : Input n) :
    (firstGate t w - firstGate u w) ^ 2 = firstGate t w + firstGate u w - 2 * (firstGate t w *
        firstGate u w) := by
  classical
  rcases first_gate_binary (w t.p) (w t.q) with ht | ht <;>
    rcases first_gate_binary (w u.p) (w u.q) with hu | hu <;> norm_num [firstGate, ht, hu]

private theorem first_gate_mean {μ : Laws n} (hsum : ∀ i, ∑ a, μ i a = 1) (t : Roles n) :
    productExpectation μ (firstGate t) = highMarginal μ t.p * lowMarginal μ t.q := by
  classical
  change productExpectation μ (fun w => highIndicator (w t.p) * lowIndicator (w t.q)) =
      highMarginal μ t.p * lowMarginal μ t.q
  simpa only [high_indicator_mean, low_indicator_mean] using product_expectation_two_positions
      hsum t.p t.q (ne_of_lt t.pq) highIndicator lowIndicator

private theorem first_gate_sq_expectation {μ : Laws n} (hsum : ∀ i, ∑ a, μ i a = 1) (t u : Roles
    n) :
    productExpectation μ (fun w => (firstGate t w - firstGate u w) ^ 2) =
      highMarginal μ t.p * lowMarginal μ t.q + highMarginal μ u.p * lowMarginal μ u.q - 2 *
          productExpectation μ (fun w => firstGate t w * firstGate u w) := by
  classical
  have h := product_expectation_linear_combination (μ := μ) (firstGate t) (firstGate u) (fun w =>
      firstGate t w * firstGate u w) 1 1 (-2)
  simp only [one_mul] at h
  rw [first_gate_mean hsum, first_gate_mean hsum] at h
  convert h using 1
  · congr 1
    funext w
    rw [first_gate_sq_eq_discrepancy]
    ring
  · ring

private theorem high_indicator_repeat (a b c : Window) :
    (highIndicator a * lowIndicator b) * (highIndicator a * lowIndicator c) = highIndicator a *
        lowIndicator b * lowIndicator c := by
  classical
  rcases (endpoint_indicators_binary a).1 with h | h <;> simp [h, mul_assoc]

private theorem low_indicator_repeat (a b c : Window) :
    (highIndicator a * lowIndicator c) * (highIndicator b * lowIndicator c) = highIndicator a *
        highIndicator b * lowIndicator c := by
  classical
  rcases (endpoint_indicators_binary c).2 with h | h <;> simp [h, mul_assoc]

private theorem first_gate_same_second_discrepancy {μ : Laws n} (hsum : ∀ i, ∑ a, μ i a = 1)
    (t u : Roles n) (hq : t.q = u.q) (hp : t.p ≠ u.p) :
    productExpectation μ (fun w => (firstGate t w - firstGate u w) ^ 2) =
      lowMarginal μ t.q * (highMarginal μ t.p + highMarginal μ u.p - 2 * highMarginal μ t.p *
          highMarginal μ u.p) := by
  classical
  have hcross : productExpectation μ (fun w => firstGate t w * firstGate u w) =
      highMarginal μ t.p * highMarginal μ u.p * lowMarginal μ t.q := by
    have heq : (fun w => firstGate t w * firstGate u w) =
        (fun w => highIndicator (w t.p) * highIndicator (w u.p) * lowIndicator (w t.q)) := by
      funext w
      simp only [firstGate, ← hq]
      exact low_indicator_repeat _ _ _
    rw [heq]
    simpa [high_indicator_mean, low_indicator_mean] using product_expectation_three_positions hsum
        t.p u.p t.q hp
      (ne_of_lt t.pq) (by simpa [hq] using ne_of_lt u.pq) highIndicator highIndicator lowIndicator
  rw [first_gate_sq_expectation hsum, hcross, ← hq]
  ring

private theorem same_tail_sq_eq_first_gate_sq {μ : Laws n} (t u : Roles n) (hq : t.q = u.q) (hr' :
    t.r = u.r) :
    distance μ t u = productExpectation μ (fun w => (firstGate t w - firstGate u w) ^ 2) := by
  classical
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [class_value_formula, class_value_formula, ← hq, ← hr']
  rcases first_gate_binary (w t.q) (w t.r) with hb | hb <;> rw [hb] <;> ring

theorem endpoint_marginal_bounds (rho : ℝ) (μ : Laws n) (hμ : Admissible rho μ) (i : Fin n) :
    (2 * rho ≤ highMarginal μ i ∧ highMarginal μ i ≤ 1 - 3 * rho) ∧
    (2 * rho ≤ lowMarginal μ i ∧ lowMarginal μ i ≤ 1 - 3 * rho) := by
  classical
  have ht := hμ.1 i .ends
  have hz := hμ.1 i .high
  have hx := hμ.1 i .low
  have hu := hμ.1 i .zero
  have hv := hμ.1 i .middle
  have hs := hμ.2 i
  simp [Finset.univ, Fintype.elems] at hs
  dsimp [highMarginal, lowMarginal]
  constructor <;> constructor <;> linarith

theorem bernoulli_discrepancy_lower (rho : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8) (s t : ℝ)
    (hs : 2 * rho ≤ s ∧ s ≤ 1 - 3 * rho)
    (ht : 2 * rho ≤ t ∧ t ≤ 1 - 3 * rho) :
    4 * rho * (1 - 2 * rho) ≤ s + t - 2 * s * t := by
  convert bernoulli_discrepancy_rectangle_lower (2 * rho) (1 - 3 * rho) s t
    (by linarith) hs ht (by linarith) (by linarith) using 1 <;> ring

set_option maxHeartbeats 2000000 in
-- The crossed and disjoint estimates normalize simultaneous mass constraints.
/-- Distinct first position pairs have first-gate discrepancy at least gamma. -/
theorem first_gate_discrepancy_lower (rho : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8)
    (μ : Laws n) (hμ : Admissible rho μ) (t u : Roles n)
    (hpairs : t.p ≠ u.p ∨ t.q ≠ u.q) :
    gamma rho ≤ productExpectation μ (fun w => (firstGate t w - firstGate u w) ^ 2) := by
  classical
  have endpoint_marginal_bounds := endpoint_marginal_bounds rho μ hμ
  have marginal0 (i : Fin n) : 0 ≤ highMarginal μ i ∧ 0 ≤ lowMarginal μ i := by
    constructor <;> linarith [(endpoint_marginal_bounds i).1.1, (endpoint_marginal_bounds i).2.1]
  have bernoulli_discrepancy_lower := bernoulli_discrepancy_lower rho hr hr8
  have common_bound (a s t : ℝ) (ha : 2 * rho ≤ a)
      (hs : 2 * rho ≤ s ∧ s ≤ 1 - 3 * rho)
      (ht : 2 * rho ≤ t ∧ t ≤ 1 - 3 * rho) :
      gamma rho ≤ a * (s + t - 2 * s * t) := by
    have hp := bernoulli_discrepancy_lower s t hs ht
    have hp0 : 0 ≤ s + t - 2 * s * t := by
      have h := mul_nonneg hr.le (show 0 ≤ 1 - 2 * rho by linarith)
      linarith
    have h1 := mul_nonneg (sub_nonneg.mpr ha) hp0
    have h2 := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * rho by linarith)
    dsimp [gamma]
    nlinarith
  by_cases hp : t.p = u.p
  · have hq : t.q ≠ u.q := by rcases hpairs with h | h <;> simp_all
    have hcross : productExpectation μ (fun w => firstGate t w * firstGate u w) =
        highMarginal μ t.p * lowMarginal μ t.q * lowMarginal μ u.q := by
      have heq : (fun w => firstGate t w * firstGate u w) =
          (fun w => highIndicator (w t.p) * lowIndicator (w t.q) * lowIndicator (w u.q)) := by
        funext w
        simp only [firstGate, ← hp]
        exact high_indicator_repeat _ _ _
      rw [heq]
      simpa [high_indicator_mean, low_indicator_mean] using product_expectation_three_positions
          hμ.2 t.p t.q u.q
        (ne_of_lt t.pq) (by simpa [hp] using ne_of_lt u.pq) hq highIndicator lowIndicator
            lowIndicator
    have he : productExpectation μ (fun w => (firstGate t w - firstGate u w) ^ 2) =
        highMarginal μ t.p * (lowMarginal μ t.q + lowMarginal μ u.q - 2 * lowMarginal μ t.q *
            lowMarginal μ u.q) := by
      rw [first_gate_sq_expectation hμ.2, hcross, ← hp]
      ring
    rw [he]
    exact (common_bound _ _ _ (endpoint_marginal_bounds t.p).1.1
      (endpoint_marginal_bounds t.q).2 (endpoint_marginal_bounds u.q).2)
  · by_cases hq : t.q = u.q
    · rw [first_gate_same_second_discrepancy hμ.2 t u hq hp]
      exact (common_bound _ _ _ (endpoint_marginal_bounds t.q).2.1
        (endpoint_marginal_bounds t.p).1 (endpoint_marginal_bounds u.p).1)
    · have cross_bound (v w : Roles n) (hcross : v.q = w.p) :
          gamma rho ≤ productExpectation μ (fun x => (firstGate v x - firstGate w x) ^ 2) := by
        have hpr : v.p ≠ w.q := ne_of_lt (lt_trans v.pq (by simpa [hcross] using w.pq))
        have he : productExpectation μ (fun x => firstGate v x * firstGate w x) =
            highMarginal μ v.p * μ v.q .ends * lowMarginal μ w.q := by
          have heq : (fun x => firstGate v x * firstGate w x) =
              (fun x => highIndicator (x v.p) * (lowIndicator (x v.q) * highIndicator (x v.q)) *
                  lowIndicator (x w.q)) := by
            funext x
            simp only [firstGate, ← hcross]
            ring
          rw [heq]
          simpa [high_indicator_mean, low_indicator_mean, joint_endpoint_mean] using
              product_expectation_three_positions hμ.2 v.p v.q w.q
            (ne_of_lt v.pq) hpr (by simpa [hcross] using ne_of_lt w.pq)
            highIndicator (fun a => lowIndicator a * highIndicator a) lowIndicator
        rw [first_gate_sq_expectation hμ.2, he, ← hcross]
        have hpsi := bernoulli_discrepancy_lower (highMarginal μ v.p) (lowMarginal μ w.q)
            (endpoint_marginal_bounds v.p).1 (endpoint_marginal_bounds w.q).2
        have hpsi0 : 0 ≤ highMarginal μ v.p + lowMarginal μ w.q - 2 * highMarginal μ v.p *
            lowMarginal μ w.q := by
          have h := mul_nonneg hr.le (show 0 ≤ 1 - 2 * rho by linarith)
          linarith
        have h1 := mul_le_mul_of_nonneg_left (hμ.1 v.q .low) (marginal0 v.p).1
        have h2 := mul_le_mul_of_nonneg_left (hμ.1 v.q .high) (marginal0 w.q).2
        have h3 := mul_le_mul_of_nonneg_right (hμ.1 v.q .ends) hpsi0
        have h4 := mul_le_mul_of_nonneg_left hpsi hr.le
        have h5 := mul_le_mul_of_nonneg_left (endpoint_marginal_bounds v.p).1.1 hr.le
        have h6 := mul_le_mul_of_nonneg_left (endpoint_marginal_bounds w.q).2.1 hr.le
        dsimp [gamma, highMarginal, lowMarginal] at *
        nlinarith
      by_cases hx : t.q = u.p
      · exact (cross_bound t u hx)
      by_cases hy : u.q = t.p
      · have h := cross_bound u t hy
        have heq : (fun w => (firstGate u w - firstGate t w) ^ 2) =
            (fun w => (firstGate t w - firstGate u w) ^ 2) := by funext w; ring
        rw [heq] at h
        exact h
      have hcross : productExpectation μ (fun w => firstGate t w * firstGate u w) =
          highMarginal μ t.p * lowMarginal μ t.q * highMarginal μ u.p * lowMarginal μ u.q := by
        have heq : (fun w => firstGate t w * firstGate u w) =
            (fun w => highIndicator (w t.p) * lowIndicator (w t.q) * highIndicator (w u.p) *
                lowIndicator (w u.q)) := by
          funext w
          dsimp [firstGate]
          ring
        rw [heq]
        simpa [high_indicator_mean, low_indicator_mean] using product_expectation_four_positions
            hμ.2 t.p t.q u.p u.q
          (ne_of_lt t.pq) hp (Ne.symm hy) hx hq (ne_of_lt u.pq) highIndicator lowIndicator
              highIndicator lowIndicator
      have product_range (i j : Fin n) :
          4 * rho ^ 2 ≤ highMarginal μ i * lowMarginal μ j ∧ highMarginal μ i * lowMarginal μ j ≤
              (1 - 3 * rho) ^ 2 := by
        have h1 := mul_le_mul (endpoint_marginal_bounds i).1.1 (endpoint_marginal_bounds j).2.1
          (show 0 ≤ 2 * rho by linarith) (marginal0 i).1
        have h2 := mul_le_mul (endpoint_marginal_bounds i).1.2 (endpoint_marginal_bounds j).2.2
          (marginal0 j).2 (show 0 ≤ 1 - 3 * rho by linarith)
        constructor <;> nlinarith
      have hr2 : rho ^ 2 ≤ rho / 8 := by
        nlinarith [mul_nonneg hr.le (show 0 ≤ 1 / 8 - rho by linarith)]
      have hbc := mul_nonneg (show 0 ≤ 1 - 5 * rho by linarith)
        (show 0 ≤ 1 - rho by linarith)
      have hmin := bernoulli_discrepancy_rectangle_lower (4 * rho ^ 2) ((1 - 3 * rho) ^ 2)
        (highMarginal μ t.p * lowMarginal μ t.q) (highMarginal μ u.p * lowMarginal μ u.q)
        (by nlinarith [hbc])
        (product_range _ _) (product_range _ _) (by nlinarith) (by nlinarith)
      have htail := mul_nonneg (sq_nonneg rho)
        (show 0 ≤ 2 * rho - 4 * rho ^ 2 by nlinarith)
      have he := first_gate_sq_expectation hμ.2 t u
      rw [hcross] at he
      dsimp [gamma]
      nlinarith

set_option maxHeartbeats 2000000 in
-- The single proof checks every overlap role and the sharpness construction together.
/-- All admissible heterogeneous laws have the same sharp lower bound, attained by a
common law and two distinct increasing triples. Positions in Roles start at zero. -/
theorem result (n : ℕ) (hn : 4 ≤ n) (rho : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8) :
    (∀ μ : Laws n, Admissible rho μ → ∀ t u : Roles n, t ≠ u →
      gamma rho ≤ distance μ t u) ∧
    (Admissible rho (fun _ => extremal rho : Laws n) ∧ ∃ t u : Roles n,
      t ≠ u ∧ distance (fun _ => extremal rho) t u = gamma rho) := by
  classical
  have lower (μ : Laws n) (hμ : Admissible rho μ) (t u : Roles n) (htu : t ≠ u) :
      gamma rho ≤ distance μ t u := by
    have positive (i : Fin n) (a : Window) : 0 ≤ μ i a := hr.le.trans (hμ.1 i a)
    have endpoint_marginal_bounds := endpoint_marginal_bounds rho μ hμ
    have bernoulli_discrepancy_lower := bernoulli_discrepancy_lower rho hr hr8
    have weighted_le (f g : Input n → ℝ) (hfg : ∀ w, f w ≤ g w) : productExpectation μ f ≤
        productExpectation μ g := by
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_mul_of_nonneg_left (hfg w)
        (Finset.prod_nonneg (fun i _ => positive i (w i)))
    have gate_le : productExpectation μ (fun w => (firstGate t w - firstGate u w) ^ 2) ≤ distance
        μ t u :=
      weighted_le _ _ (first_gate_sq_le_class_sq t u)
    by_cases hp : t.p = u.p
    · by_cases hq : t.q = u.q
      · have hrne : t.r ≠ u.r := by
          intro he
          apply htu
          cases t
          cases u
          simp_all
        let z (a : Window) : ℝ := if a = .high then 1 else 0
        have zmean (i : Fin n) : (∑ a, μ i a * z a) = μ i .high := by
          simp [Finset.univ, Fintype.elems, z]
        have point (w : Input n) :
            4 * (z (w t.q) * lowIndicator (w t.r) + z (w t.q) * lowIndicator (w u.r) -
              2 * (z (w t.q) * lowIndicator (w t.r) * lowIndicator (w u.r))) ≤
                (classValue t w - classValue u w) ^ 2 := by
          by_cases hw : w t.q = .high
          · rw [class_value_formula, class_value_formula]
            simp only [firstGate, ← hp, ← hq, hw]
            have hhi : highIndicator .high = 1 := rfl
            have hlo : lowIndicator .high = 0 := rfl
            have hz : z .high = 1 := by simp [z]
            simp only [hhi, hlo, hz, mul_zero, zero_mul, sub_zero, zero_add, one_mul]
            rcases (endpoint_indicators_binary (w t.r)).2 with ha | ha <;>
              rcases (endpoint_indicators_binary (w u.r)).2 with hb | hb <;> norm_num [ha, hb]
          · simp [z, hw, sq_nonneg]
        have he : productExpectation μ (fun w => 4 * (z (w t.q) * lowIndicator (w t.r) +
            z (w t.q) * lowIndicator (w u.r) - 2 * (z (w t.q) * lowIndicator (w t.r) *
                lowIndicator (w u.r)))) =
            4 * μ t.q .high * (lowMarginal μ t.r + lowMarginal μ u.r - 2 * lowMarginal μ t.r *
                lowMarginal μ u.r) := by
          have h := product_expectation_linear_combination (μ := μ) (fun w => z (w t.q) *
              lowIndicator (w t.r))
            (fun w => z (w t.q) * lowIndicator (w u.r))
            (fun w => z (w t.q) * lowIndicator (w t.r) * lowIndicator (w u.r)) 4 4 (-8)
          rw [product_expectation_two_positions hμ.2 _ _ (ne_of_lt t.qr),
            product_expectation_two_positions hμ.2 _ _ (by simpa [hq] using ne_of_lt u.qr),
            product_expectation_three_positions hμ.2 _ _ _ (ne_of_lt t.qr)
              (by simpa [hq] using ne_of_lt u.qr) hrne] at h
          simp only [zmean, low_indicator_mean] at h
          convert h using 1
          · congr 1
            funext w
            ring
          · ring
        have hh := weighted_le _ _ point
        rw [he] at hh
        have hp := bernoulli_discrepancy_lower (lowMarginal μ t.r) (lowMarginal μ u.r)
            (endpoint_marginal_bounds t.r).2 (endpoint_marginal_bounds u.r).2
        have hpp : 0 ≤ lowMarginal μ t.r + lowMarginal μ u.r - 2 * lowMarginal μ t.r * lowMarginal
            μ u.r := by
          have h := mul_nonneg hr.le (show 0 ≤ 1 - 2 * rho by linarith)
          linarith
        have h1 := mul_le_mul_of_nonneg_right (hμ.1 t.q .high) hpp
        have h2 := mul_le_mul_of_nonneg_left hp hr.le
        dsimp [gamma]
        change _ ≤ productExpectation μ (fun w => (classValue t w - classValue u w) ^ 2)
        nlinarith
      · exact (first_gate_discrepancy_lower rho hr hr8 μ hμ t u (Or.inr hq)).trans gate_le
    · exact (first_gate_discrepancy_lower rho hr hr8 μ hμ t u (Or.inl hp)).trans gate_le
  refine ⟨lower, ?_⟩
  let μ : Laws n := fun _ => extremal rho
  have hm : Admissible rho μ := by
    constructor
    · intro i a
      cases a <;> dsimp [μ, extremal] <;> linarith
    · intro i
      simp [μ, Finset.univ, Fintype.elems, extremal]
      ring
  let t : Roles n := ⟨⟨0, by omega⟩, ⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩,
    by change 0 < n - 2; omega, by change n - 2 < n - 1; omega⟩
  let u : Roles n := ⟨⟨1, by omega⟩, ⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩,
    by change 1 < n - 2; omega, by change n - 2 < n - 1; omega⟩
  have hp : t.p ≠ u.p := by
    intro h
    have := congrArg Fin.val h
    norm_num [t, u] at this
  refine ⟨hm, t, u, (fun he => hp (congrArg Roles.p he)), ?_⟩
  rw [same_tail_sq_eq_first_gate_sq t u rfl rfl, first_gate_same_second_discrepancy hm.2 t u rfl
      hp]
  norm_num [μ, highMarginal, lowMarginal, extremal, gamma]
  ring

end D5.S3.Arith.FibonacciAtomic.HeterogeneousTeacherSeparation
