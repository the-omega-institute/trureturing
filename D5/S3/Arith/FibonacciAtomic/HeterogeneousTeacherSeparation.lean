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
def E {n : ℕ} (μ : Laws n) (f : Input n → ℝ) : ℝ :=
  ∑ w : Input n, (∏ i, μ i (w i)) * f w

/-- High endpoint indicator. -/
def hi (a : Window) : ℝ := if last a then 1 else 0

/-- Low endpoint indicator. -/
def lo (a : Window) : ℝ := if first a then 1 else 0

/-- High endpoint marginal in one actual window. -/
def H {n : ℕ} (μ : Laws n) (i : Fin n) : ℝ := μ i .ends + μ i .high

/-- Low endpoint marginal in one actual window. -/
def L {n : ℕ} (μ : Laws n) (i : Fin n) : ℝ := μ i .ends + μ i .low

/-- First priority gate. -/
def G {n : ℕ} (t : Roles n) (w : Input n) : ℝ := hi (w t.p) * lo (w t.q)

variable {n : ℕ}

private theorem factor {μ : Laws n} (hsum : ∀ i, ∑ a, μ i a = 1)
    (S : Finset (Fin n)) (f : Fin n → Window → ℝ) :
    E μ (fun w => ∏ i ∈ S, f i (w i)) = ∏ i ∈ S, ∑ a, μ i a * f i a := by
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
    by_cases hi : i ∈ S <;> simp [hi, hsum]
  simpa only [E, hl, hr, Finset.prod_ite_mem, Finset.univ_inter] using h

theorem two {μ : Laws n} (hsum : ∀ i, ∑ a, μ i a = 1)
    (p q : Fin n) (hpq : p ≠ q) (f g : Window → ℝ) :
    E μ (fun w => f (w p) * g (w q)) =
      (∑ a, μ p a * f a) * (∑ a, μ q a * g a) := by
  classical
  simpa [hpq, Ne.symm hpq] using
    factor hsum {p, q} (fun i a => if i = p then f a else g a)

theorem three {μ : Laws n} (hsum : ∀ i, ∑ a, μ i a = 1)
    (p q r : Fin n) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (f g h : Window → ℝ) :
    E μ (fun w => f (w p) * g (w q) * h (w r)) =
      (∑ a, μ p a * f a) * (∑ a, μ q a * g a) * (∑ a, μ r a * h a) := by
  classical
  simpa [hpq, hpr, hqr, Ne.symm hpq, Ne.symm hpr, Ne.symm hqr, mul_assoc] using
    factor hsum {p, q, r} (fun i a => if i = p then f a else if i = q then g a else h a)

theorem four {μ : Laws n} (hsum : ∀ i, ∑ a, μ i a = 1)
    (p q r s : Fin n) (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) (f g h k : Window → ℝ) :
    E μ (fun w => f (w p) * g (w q) * h (w r) * k (w s)) =
      (∑ a, μ p a * f a) * (∑ a, μ q a * g a) *
        (∑ a, μ r a * h a) * (∑ a, μ s a * k a) := by
  classical
  simpa [hpq, hpr, hps, hqr, hqs, hrs, Ne.symm hpq, Ne.symm hpr,
    Ne.symm hps, Ne.symm hqr, Ne.symm hqs, Ne.symm hrs, mul_assoc] using
    factor hsum {p, q, r, s} (fun i a => if i = p then f a else if i = q then g a
      else if i = r then h a else k a)

theorem linear {μ : Laws n} (f g h : Input n → ℝ) (a b c : ℝ) :
    E μ (fun w => a * f w + b * g w + c * h w) = a * E μ f + b * E μ g + c * E μ h := by
  classical
  have scale (d : ℝ) (f : Input n → ℝ) : E μ (fun w => d * f w) = d * E μ f := by
    dsimp [E]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  calc
    _ = E μ (fun w => a * f w) + E μ (fun w => b * g w) +
        E μ (fun w => c * h w) := by simp [E, mul_add, Finset.sum_add_distrib]
    _ = _ := by rw [scale, scale, scale]

private theorem corners (b c s t : ℝ) (hbc : b ≤ c) (hs : b ≤ s ∧ s ≤ c)
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

theorem univ : (Finset.univ : Finset Window) = {.zero, .low, .middle, .ends, .high} := rfl

theorem high_mean (μ : Laws n) (i : Fin n) : (∑ a, μ i a * hi a) = H μ i := by
  classical
  simp [univ, hi, last, H]

theorem low_mean (μ : Laws n) (i : Fin n) : (∑ a, μ i a * lo a) = L μ i := by
  classical
  simp [univ, lo, first, L, add_comm]

theorem joint_mean (μ : Laws n) (i : Fin n) : (∑ a, μ i a * (lo a * hi a)) = μ i .ends := by
  classical
  simp [univ, hi, lo, first, last]

theorem binary (a : Window) : (hi a = 0 ∨ hi a = 1) ∧ (lo a = 0 ∨ lo a = 1) := by
  classical
  cases a <;> simp [hi, lo, first, last]

theorem gate_binary (a b : Window) : hi a * lo b = 0 ∨ hi a * lo b = 1 := by
  classical
  rcases (binary a).1 with ha | ha <;>
    rcases (binary b).2 with hb | hb <;> simp [ha, hb]

theorem class_formula (t : Roles n) (w : Input n) :
    classValue t w = G t w + 2 * (1 - G t w) * (hi (w t.q) * lo (w t.r)) := by
  classical
  cases hp : last (w t.p) <;> cases hq : first (w t.q) <;>
    cases hq' : last (w t.q) <;> cases hr' : first (w t.r) <;>
    norm_num [classValue, GarbledPosteriorRootGap.teacher, Matrix.cons_val_two,
      G, hi, lo, hp, hq, hq', hr']

private theorem gate_point (t u : Roles n) (w : Input n) :
    (G t w - G u w) ^ 2 ≤ (classValue t w - classValue u w) ^ 2 := by
  classical
  rw [class_formula, class_formula]
  rcases gate_binary (w t.p) (w t.q) with ht | ht <;>
    rcases gate_binary (w u.p) (w u.q) with hu | hu <;>
    rcases gate_binary (w t.q) (w t.r) with hb | hb <;>
    rcases gate_binary (w u.q) (w u.r) with hc | hc <;>
    norm_num [G, ht, hu, hb, hc]

private theorem gate_square (t u : Roles n) (w : Input n) :
    (G t w - G u w) ^ 2 = G t w + G u w - 2 * (G t w * G u w) := by
  classical
  rcases gate_binary (w t.p) (w t.q) with ht | ht <;>
    rcases gate_binary (w u.p) (w u.q) with hu | hu <;> norm_num [G, ht, hu]

private theorem gate_mean {μ : Laws n} (hsum : ∀ i, ∑ a, μ i a = 1) (t : Roles n) :
    E μ (G t) = H μ t.p * L μ t.q := by
  classical
  change E μ (fun w => hi (w t.p) * lo (w t.q)) = H μ t.p * L μ t.q
  simpa only [high_mean, low_mean] using two hsum t.p t.q (ne_of_lt t.pq) hi lo

private theorem gate_distance {μ : Laws n} (hsum : ∀ i, ∑ a, μ i a = 1) (t u : Roles n) :
    E μ (fun w => (G t w - G u w) ^ 2) =
      H μ t.p * L μ t.q + H μ u.p * L μ u.q - 2 * E μ (fun w => G t w * G u w) := by
  classical
  have h := linear (μ := μ) (G t) (G u) (fun w => G t w * G u w) 1 1 (-2)
  simp only [one_mul] at h
  rw [gate_mean hsum, gate_mean hsum] at h
  convert h using 1
  · congr 1
    funext w
    rw [gate_square]
    ring
  · ring

private theorem merge_first (a b c : Window) :
    (hi a * lo b) * (hi a * lo c) = hi a * lo b * lo c := by
  classical
  rcases (binary a).1 with h | h <;> simp [h, mul_assoc]

private theorem merge_second (a b c : Window) :
    (hi a * lo c) * (hi b * lo c) = hi a * hi b * lo c := by
  classical
  rcases (binary c).2 with h | h <;> simp [h, mul_assoc]

private theorem same_second {μ : Laws n} (hsum : ∀ i, ∑ a, μ i a = 1)
    (t u : Roles n) (hq : t.q = u.q) (hp : t.p ≠ u.p) :
    E μ (fun w => (G t w - G u w) ^ 2) =
      L μ t.q * (H μ t.p + H μ u.p - 2 * H μ t.p * H μ u.p) := by
  classical
  have hcross : E μ (fun w => G t w * G u w) =
      H μ t.p * H μ u.p * L μ t.q := by
    have heq : (fun w => G t w * G u w) =
        (fun w => hi (w t.p) * hi (w u.p) * lo (w t.q)) := by
      funext w
      simp only [G, ← hq]
      exact merge_second _ _ _
    rw [heq]
    simpa [high_mean, low_mean] using three hsum t.p u.p t.q hp
      (ne_of_lt t.pq) (by simpa [hq] using ne_of_lt u.pq) hi hi lo
  rw [gate_distance hsum, hcross, ← hq]
  ring

private theorem same_tail {μ : Laws n} (t u : Roles n) (hq : t.q = u.q) (hr' : t.r = u.r) :
    distance μ t u = E μ (fun w => (G t w - G u w) ^ 2) := by
  classical
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [class_formula, class_formula, ← hq, ← hr']
  rcases gate_binary (w t.q) (w t.r) with hb | hb <;> rw [hb] <;> ring

theorem marginal (rho : ℝ) (μ : Laws n) (hμ : Admissible rho μ) (i : Fin n) :
    (2 * rho ≤ H μ i ∧ H μ i ≤ 1 - 3 * rho) ∧
    (2 * rho ≤ L μ i ∧ L μ i ≤ 1 - 3 * rho) := by
  classical
  have ht := hμ.1 i .ends
  have hz := hμ.1 i .high
  have hx := hμ.1 i .low
  have hu := hμ.1 i .zero
  have hv := hμ.1 i .middle
  have hs := hμ.2 i
  simp [univ] at hs
  dsimp [H, L]
  constructor <;> constructor <;> linarith

theorem psi (rho : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8) (s t : ℝ)
    (hs : 2 * rho ≤ s ∧ s ≤ 1 - 3 * rho)
    (ht : 2 * rho ≤ t ∧ t ≤ 1 - 3 * rho) :
    4 * rho * (1 - 2 * rho) ≤ s + t - 2 * s * t := by
  convert corners (2 * rho) (1 - 3 * rho) s t
    (by linarith) hs ht (by linarith) (by linarith) using 1 <;> ring

set_option maxHeartbeats 2000000 in
-- The crossed and disjoint estimates normalize simultaneous mass constraints.
/-- Distinct first position pairs have first-gate discrepancy at least gamma. -/
theorem gate_lower (rho : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8)
    (μ : Laws n) (hμ : Admissible rho μ) (t u : Roles n)
    (hpairs : t.p ≠ u.p ∨ t.q ≠ u.q) :
    gamma rho ≤ E μ (fun w => (G t w - G u w) ^ 2) := by
  classical
  have marginal := marginal rho μ hμ
  have marginal0 (i : Fin n) : 0 ≤ H μ i ∧ 0 ≤ L μ i := by
    constructor <;> linarith [(marginal i).1.1, (marginal i).2.1]
  have psi := psi rho hr hr8
  have common_bound (a s t : ℝ) (ha : 2 * rho ≤ a)
      (hs : 2 * rho ≤ s ∧ s ≤ 1 - 3 * rho)
      (ht : 2 * rho ≤ t ∧ t ≤ 1 - 3 * rho) :
      gamma rho ≤ a * (s + t - 2 * s * t) := by
    have hp := psi s t hs ht
    have hp0 : 0 ≤ s + t - 2 * s * t := by
      have h := mul_nonneg hr.le (show 0 ≤ 1 - 2 * rho by linarith)
      linarith
    have h1 := mul_nonneg (sub_nonneg.mpr ha) hp0
    have h2 := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * rho by linarith)
    dsimp [gamma]
    nlinarith
  by_cases hp : t.p = u.p
  · have hq : t.q ≠ u.q := by rcases hpairs with h | h <;> simp_all
    have hcross : E μ (fun w => G t w * G u w) =
        H μ t.p * L μ t.q * L μ u.q := by
      have heq : (fun w => G t w * G u w) =
          (fun w => hi (w t.p) * lo (w t.q) * lo (w u.q)) := by
        funext w
        simp only [G, ← hp]
        exact merge_first _ _ _
      rw [heq]
      simpa [high_mean, low_mean] using three hμ.2 t.p t.q u.q
        (ne_of_lt t.pq) (by simpa [hp] using ne_of_lt u.pq) hq hi lo lo
    have he : E μ (fun w => (G t w - G u w) ^ 2) =
        H μ t.p * (L μ t.q + L μ u.q - 2 * L μ t.q * L μ u.q) := by
      rw [gate_distance hμ.2, hcross, ← hp]
      ring
    rw [he]
    exact (common_bound _ _ _ (marginal t.p).1.1
      (marginal t.q).2 (marginal u.q).2)
  · by_cases hq : t.q = u.q
    · rw [same_second hμ.2 t u hq hp]
      exact (common_bound _ _ _ (marginal t.q).2.1
        (marginal t.p).1 (marginal u.p).1)
    · have cross_bound (v w : Roles n) (hcross : v.q = w.p) :
          gamma rho ≤ E μ (fun x => (G v x - G w x) ^ 2) := by
        have hpr : v.p ≠ w.q := ne_of_lt (lt_trans v.pq (by simpa [hcross] using w.pq))
        have he : E μ (fun x => G v x * G w x) =
            H μ v.p * μ v.q .ends * L μ w.q := by
          have heq : (fun x => G v x * G w x) =
              (fun x => hi (x v.p) * (lo (x v.q) * hi (x v.q)) * lo (x w.q)) := by
            funext x
            simp only [G, ← hcross]
            ring
          rw [heq]
          simpa [high_mean, low_mean, joint_mean] using three hμ.2 v.p v.q w.q
            (ne_of_lt v.pq) hpr (by simpa [hcross] using ne_of_lt w.pq)
            hi (fun a => lo a * hi a) lo
        rw [gate_distance hμ.2, he, ← hcross]
        have hpsi := psi (H μ v.p) (L μ w.q) (marginal v.p).1 (marginal w.q).2
        have hpsi0 : 0 ≤ H μ v.p + L μ w.q - 2 * H μ v.p * L μ w.q := by
          have h := mul_nonneg hr.le (show 0 ≤ 1 - 2 * rho by linarith)
          linarith
        have h1 := mul_le_mul_of_nonneg_left (hμ.1 v.q .low) (marginal0 v.p).1
        have h2 := mul_le_mul_of_nonneg_left (hμ.1 v.q .high) (marginal0 w.q).2
        have h3 := mul_le_mul_of_nonneg_right (hμ.1 v.q .ends) hpsi0
        have h4 := mul_le_mul_of_nonneg_left hpsi hr.le
        have h5 := mul_le_mul_of_nonneg_left (marginal v.p).1.1 hr.le
        have h6 := mul_le_mul_of_nonneg_left (marginal w.q).2.1 hr.le
        dsimp [gamma, H, L] at *
        nlinarith
      by_cases hx : t.q = u.p
      · exact (cross_bound t u hx)
      by_cases hy : u.q = t.p
      · have h := cross_bound u t hy
        have heq : (fun w => (G u w - G t w) ^ 2) =
            (fun w => (G t w - G u w) ^ 2) := by funext w; ring
        rw [heq] at h
        exact h
      have hcross : E μ (fun w => G t w * G u w) =
          H μ t.p * L μ t.q * H μ u.p * L μ u.q := by
        have heq : (fun w => G t w * G u w) =
            (fun w => hi (w t.p) * lo (w t.q) * hi (w u.p) * lo (w u.q)) := by
          funext w
          dsimp [G]
          ring
        rw [heq]
        simpa [high_mean, low_mean] using four hμ.2 t.p t.q u.p u.q
          (ne_of_lt t.pq) hp (Ne.symm hy) hx hq (ne_of_lt u.pq) hi lo hi lo
      have product_range (i j : Fin n) :
          4 * rho ^ 2 ≤ H μ i * L μ j ∧ H μ i * L μ j ≤ (1 - 3 * rho) ^ 2 := by
        have h1 := mul_le_mul (marginal i).1.1 (marginal j).2.1
          (show 0 ≤ 2 * rho by linarith) (marginal0 i).1
        have h2 := mul_le_mul (marginal i).1.2 (marginal j).2.2
          (marginal0 j).2 (show 0 ≤ 1 - 3 * rho by linarith)
        constructor <;> nlinarith
      have hr2 : rho ^ 2 ≤ rho / 8 := by
        nlinarith [mul_nonneg hr.le (show 0 ≤ 1 / 8 - rho by linarith)]
      have hbc := mul_nonneg (show 0 ≤ 1 - 5 * rho by linarith)
        (show 0 ≤ 1 - rho by linarith)
      have hmin := corners (4 * rho ^ 2) ((1 - 3 * rho) ^ 2)
        (H μ t.p * L μ t.q) (H μ u.p * L μ u.q)
        (by nlinarith [hbc])
        (product_range _ _) (product_range _ _) (by nlinarith) (by nlinarith)
      have htail := mul_nonneg (sq_nonneg rho)
        (show 0 ≤ 2 * rho - 4 * rho ^ 2 by nlinarith)
      have he := gate_distance hμ.2 t u
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
    have marginal := marginal rho μ hμ
    have marginal0 (i : Fin n) : 0 ≤ H μ i ∧ 0 ≤ L μ i := by
      constructor <;> linarith [(marginal i).1.1, (marginal i).2.1]
    have psi := psi rho hr hr8
    have weighted_le (f g : Input n → ℝ) (hfg : ∀ w, f w ≤ g w) : E μ f ≤ E μ g := by
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_mul_of_nonneg_left (hfg w)
        (Finset.prod_nonneg (fun i _ => positive i (w i)))
    have gate_le : E μ (fun w => (G t w - G u w) ^ 2) ≤ distance μ t u :=
      weighted_le _ _ (gate_point t u)
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
          simp [univ, z]
        have point (w : Input n) :
            4 * (z (w t.q) * lo (w t.r) + z (w t.q) * lo (w u.r) -
              2 * (z (w t.q) * lo (w t.r) * lo (w u.r))) ≤
                (classValue t w - classValue u w) ^ 2 := by
          by_cases hw : w t.q = .high
          · rw [class_formula, class_formula]
            simp only [G, ← hp, ← hq, hw]
            have hhi : hi .high = 1 := rfl
            have hlo : lo .high = 0 := rfl
            have hz : z .high = 1 := by simp [z]
            simp only [hhi, hlo, hz, mul_zero, zero_mul, sub_zero, zero_add, one_mul]
            rcases (binary (w t.r)).2 with ha | ha <;>
              rcases (binary (w u.r)).2 with hb | hb <;> norm_num [ha, hb]
          · simp [z, hw, sq_nonneg]
        have he : E μ (fun w => 4 * (z (w t.q) * lo (w t.r) +
            z (w t.q) * lo (w u.r) - 2 * (z (w t.q) * lo (w t.r) * lo (w u.r)))) =
            4 * μ t.q .high * (L μ t.r + L μ u.r - 2 * L μ t.r * L μ u.r) := by
          have h := linear (μ := μ) (fun w => z (w t.q) * lo (w t.r))
            (fun w => z (w t.q) * lo (w u.r))
            (fun w => z (w t.q) * lo (w t.r) * lo (w u.r)) 4 4 (-8)
          rw [two hμ.2 _ _ (ne_of_lt t.qr),
            two hμ.2 _ _ (by simpa [hq] using ne_of_lt u.qr),
            three hμ.2 _ _ _ (ne_of_lt t.qr)
              (by simpa [hq] using ne_of_lt u.qr) hrne] at h
          simp only [zmean, low_mean] at h
          convert h using 1
          · congr 1
            funext w
            ring
          · ring
        have hh := weighted_le _ _ point
        rw [he] at hh
        have hp := psi (L μ t.r) (L μ u.r) (marginal t.r).2 (marginal u.r).2
        have hpp : 0 ≤ L μ t.r + L μ u.r - 2 * L μ t.r * L μ u.r := by
          have h := mul_nonneg hr.le (show 0 ≤ 1 - 2 * rho by linarith)
          linarith
        have h1 := mul_le_mul_of_nonneg_right (hμ.1 t.q .high) hpp
        have h2 := mul_le_mul_of_nonneg_left hp hr.le
        dsimp [gamma]
        change _ ≤ E μ (fun w => (classValue t w - classValue u w) ^ 2)
        nlinarith
      · exact (gate_lower rho hr hr8 μ hμ t u (Or.inr hq)).trans gate_le
    · exact (gate_lower rho hr hr8 μ hμ t u (Or.inl hp)).trans gate_le
  refine ⟨lower, ?_⟩
  let μ : Laws n := fun _ => extremal rho
  have hm : Admissible rho μ := by
    constructor
    · intro i a
      cases a <;> dsimp [μ, extremal] <;> linarith
    · intro i
      simp [μ, univ, extremal]
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
  rw [same_tail t u rfl rfl, same_second hm.2 t u rfl hp]
  norm_num [μ, H, L, extremal, gamma]
  ring

end D5.S3.Arith.FibonacciAtomic.HeterogeneousTeacherSeparation
