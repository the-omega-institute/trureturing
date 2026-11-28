import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp

/-! Omega original.

# Polynomial prefix weights and the flat triangle deficit

The sums use increasing natural number indices below a finite cutoff. The only
external analytic input to the final estimate is the stated bound for the
sorted triple square sum on every prefix. Zero weights and empty prefixes are
included throughout.
-/

compile_only_with_mathlib

open scoped BigOperators
open Finset intervalIntegral

namespace HilbertPrefixDeficit

noncomputable def w : ℝ := 157 / 1000
noncomputable def c : ℝ := 39 / 5000
noncomputable def gamma : ℝ := 7800 / 11881
noncomputable def eta (t : ℝ) : ℝ :=
  1 +
  (843 / 1000 : ℝ) * (1 - t) +
  (1553649 / 2000000 : ℝ) * (1 - t) ^ 2 +
  (1472341369 / 2000000000 : ℝ) * (1 - t) ^ 3 +
  (5658207881067 / 8000000000000 : ℝ) * (1 - t) ^ 4
noncomputable def I0 : ℝ := 80237574726067 / 40000000000000
noncomputable def I : ℝ := 53817954780581 / 120000000000000
noncomputable def K : ℝ := 23687349672567 / 2000000000000
noncomputable def slope : ℝ := 14868529988067 / 2000000000000

private noncomputable def primitive (t : ℝ) : ℝ :=
  (32506169357067 / 8000000000000 : ℝ) * t ^ 1 +
  (-14868529988067 / 4000000000000 : ℝ) * t ^ 2 +
  (9638656619067 / 4000000000000 : ℝ) * t ^ 3 +
  (-7130549250067 / 8000000000000 : ℝ) * t ^ 4 +
  (5658207881067 / 40000000000000 : ℝ) * t ^ 5
private noncomputable def momentPrimitive (t : ℝ) : ℝ :=
  (10835389785689 / 8000000000000 : ℝ) * t ^ 3 +
  (-14868529988067 / 8000000000000 : ℝ) * t ^ 4 +
  (28915969857201 / 20000000000000 : ℝ) * t ^ 5 +
  (-7130549250067 / 12000000000000 : ℝ) * t ^ 6 +
  (808315411581 / 8000000000000 : ℝ) * t ^ 7

private theorem primitive_deriv (t : ℝ) : HasDerivAt primitive (eta t) t := by
  have h1 := (hasDerivAt_pow 1 t).const_mul (32506169357067 / 8000000000000 : ℝ)
  have h2 := h1.add ((hasDerivAt_pow 2 t).const_mul (-14868529988067 / 4000000000000 : ℝ))
  have h3 := h2.add ((hasDerivAt_pow 3 t).const_mul (9638656619067 / 4000000000000 : ℝ))
  have h4 := h3.add ((hasDerivAt_pow 4 t).const_mul (-7130549250067 / 8000000000000 : ℝ))
  have h5 := h4.add ((hasDerivAt_pow 5 t).const_mul (5658207881067 / 40000000000000 : ℝ))
  convert h5 using 1 <;> (try funext x) <;> norm_num [primitive, eta, Pi.add_apply]; ring

private theorem momentPrimitive_deriv (t : ℝ) :
    HasDerivAt momentPrimitive (t ^ 2 * eta t) t := by
  have h1 := (hasDerivAt_pow 3 t).const_mul (10835389785689 / 8000000000000 : ℝ)
  have h2 := h1.add ((hasDerivAt_pow 4 t).const_mul (-14868529988067 / 8000000000000 : ℝ))
  have h3 := h2.add ((hasDerivAt_pow 5 t).const_mul (28915969857201 / 20000000000000 : ℝ))
  have h4 := h3.add ((hasDerivAt_pow 6 t).const_mul (-7130549250067 / 12000000000000 : ℝ))
  have h5 := h4.add ((hasDerivAt_pow 7 t).const_mul (808315411581 / 8000000000000 : ℝ))
  convert h5 using 1 <;> (try funext x) <;> norm_num [momentPrimitive, eta, Pi.add_apply]; ring

@[fun_prop] theorem continuous_eta : Continuous eta := by unfold eta; fun_prop

private theorem integral_eta (a b : ℝ) :
    (∫ t in a..b, eta t) = primitive b - primitive a :=
  integral_eq_sub_of_hasDerivAt (fun t _ => primitive_deriv t)
    (continuous_eta.intervalIntegrable _ _)

theorem integral_eta_unit : (∫ t in (0:ℝ)..1, eta t) = I0 := by
  rw [integral_eta]; norm_num [primitive, I0]

theorem integral_moment_unit : (∫ t in (0:ℝ)..1, t ^ 2 * eta t) = I := by
  rw [integral_eq_sub_of_hasDerivAt (fun t _ => momentPrimitive_deriv t)
    ((by fun_prop : Continuous (fun t : ℝ => t ^ 2 * eta t)).intervalIntegrable _ _)]
  norm_num [momentPrimitive, I]

theorem eta_one : eta 1 = 1 := by norm_num [eta]
theorem eta_zero : eta 0 = 32506169357067 / 8000000000000 := by norm_num [eta]
theorem K_eq : K = 2 * eta 0 + slope / 2 := by norm_num [K, slope, eta]

/-- The endpoint derivative fixes the exact constant in the atom correction. -/
theorem eta_hasDerivAt_zero : HasDerivAt eta (-slope) 0 := by
  have h0 := hasDerivAt_const (0:ℝ) (32506169357067 / 8000000000000 : ℝ)
  have h1 := h0.add ((hasDerivAt_pow 1 (0:ℝ)).const_mul (-14868529988067 / 2000000000000 : ℝ))
  have h2 := h1.add ((hasDerivAt_pow 2 (0:ℝ)).const_mul (28915969857201 / 4000000000000 : ℝ))
  have h3 := h2.add ((hasDerivAt_pow 3 (0:ℝ)).const_mul (-7130549250067 / 2000000000000 : ℝ))
  have h4 := h3.add ((hasDerivAt_pow 4 (0:ℝ)).const_mul (5658207881067 / 8000000000000 : ℝ))
  convert h4 using 1 <;> (try funext x) <;> norm_num [eta, slope, Pi.add_apply]; ring

theorem K_deriv : K = 2 * eta 0 + |deriv eta 0|/2 := by
  rw [eta_hasDerivAt_zero.deriv, abs_neg, abs_of_nonneg (by norm_num [slope] : 0 ≤ slope)]
  exact K_eq

theorem eta_nonneg {t : ℝ} (ht : t ≤ 1) : 0 ≤ eta t := by
  dsimp [eta]; positivity

private theorem power_difference {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a)
    (ha : a ≤ 1) (j : ℕ) : a ^ j - b ^ j ≤ j * (a - b) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ha0 : 0 ≤ a := hb.trans hba
    have hj : 0 ≤ a ^ j - b ^ j := sub_nonneg.mpr (pow_le_pow_left₀ hb hba _)
    have hbpow : b ^ j ≤ 1 := pow_le_one₀ hb (hba.trans ha)
    have h1 := mul_le_mul_of_nonneg_right ha hj
    have h2 := mul_le_mul_of_nonneg_left hbpow (sub_nonneg.mpr hba)
    rw [pow_succ, pow_succ, Nat.cast_succ]
    nlinarith

theorem eta_antitone {s t : ℝ} (_hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    eta t ≤ eta s := by
  have h1 : 0 ≤ 1 - t := sub_nonneg.mpr ht
  have h2 : 1 - t ≤ 1 - s := by linarith
  have hpow2 := pow_le_pow_left₀ h1 h2 2
  have hpow3 := pow_le_pow_left₀ h1 h2 3
  have hpow4 := pow_le_pow_left₀ h1 h2 4
  dsimp [eta]; nlinarith

theorem eta_difference {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    eta s - eta t ≤ slope * (t - s) := by
  have h1 : 0 ≤ 1 - t := sub_nonneg.mpr ht
  have h2 : 1 - t ≤ 1 - s := by linarith
  have h3 : 1 - s ≤ 1 := by linarith
  have hpow2 := power_difference h1 h2 h3 2
  have hpow3 := power_difference h1 h2 h3 3
  have hpow4 := power_difference h1 h2 h3 4
  dsimp [eta, slope]; norm_num at hpow2 hpow3 hpow4 ⊢; nlinarith

/-- The exact identity underlying the edge coefficient bound. -/
theorem eta_identity (t : ℝ) :
    t * eta t + w * (∫ u in t..1, eta u) =
      1 - (5658207881067 / 8000000000000 : ℝ) * (1 - w/5) * (1 - t) ^ 5 := by
  rw [integral_eta]; dsimp [eta, w, primitive]; ring

/-- Equation (12), including its boundary values. -/
theorem eta_budget {t : ℝ} (ht : t ≤ 1) :
    t * eta t + w * (∫ u in t..1, eta u) ≤ 1 := by
  rw [eta_identity]; have : 0 ≤ 1 - t := sub_nonneg.mpr ht
  norm_num [w]; positivity

noncomputable def prefixMass (p : ℕ → ℝ) (m : ℕ) : ℝ := ∑ i ∈ range m, p i
noncomputable def squares (p : ℕ → ℝ) (m : ℕ) : ℝ := ∑ i ∈ range m, (p i) ^ 2
noncomputable def pairs (p : ℕ → ℝ) (d : ℕ → ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ range m, ∑ i ∈ range j, p i * p j * d i j
noncomputable def triples (p : ℕ → ℝ) (h : ℕ → ℕ → ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ range m, ∑ j ∈ range k, ∑ i ∈ range j, 2 * p i * p j * p k * h i j k
noncomputable def weightedTriples (p : ℕ → ℝ) (h : ℕ → ℕ → ℕ → ℝ)
    (m : ℕ) : ℝ :=
  ∑ k ∈ range m, eta (prefixMass p (k + 1)) *
    (∑ j ∈ range k, ∑ i ∈ range j, 2 * p i * p j * p k * h i j k)

@[simp] theorem prefix_zero (p : ℕ → ℝ) : prefixMass p 0 = 0 := by simp [prefixMass]
theorem prefix_succ (p : ℕ → ℝ) (m : ℕ) :
    prefixMass p (m + 1) = prefixMass p m + p m := by simp [prefixMass, sum_range_succ]

private theorem prefix_nonneg {p : ℕ → ℝ} {n m : ℕ}
    (hp : ∀ i < n, 0 ≤ p i) (hm : m ≤ n) : 0 ≤ prefixMass p m :=
  sum_nonneg fun i hi => hp i (lt_of_lt_of_le (mem_range.mp hi) hm)

private theorem prefix_mono {p : ℕ → ℝ} {n a b : ℕ}
    (hp : ∀ i < n, 0 ≤ p i) (hab : a ≤ b) (hb : b ≤ n) :
    prefixMass p a ≤ prefixMass p b := by
  exact sum_le_sum_of_subset_of_nonneg (range_mono hab)
    (fun i hi _ => hp i (lt_of_lt_of_le (mem_range.mp hi) hb))

private theorem prefix_le_one {p : ℕ → ℝ} {n m : ℕ}
    (hp : ∀ i < n, 0 ≤ p i) (hmass : prefixMass p n = 1) (hm : m ≤ n) :
    prefixMass p m ≤ 1 := hmass ▸ prefix_mono hp hm le_rfl

private theorem squares_mono (p : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    squares p a ≤ squares p b :=
  sum_le_sum_of_subset_of_nonneg (range_mono hab) (fun i _ _ => sq_nonneg (p i))

private theorem pair_constant (p : ℕ → ℝ) (m : ℕ) :
    2 * pairs p (fun _ _ => 1) m = (prefixMass p m) ^ 2 - squares p m := by
  induction m with
  | zero => simp [pairs, prefixMass, squares]
  | succ m ih =>
    simp only [pairs, sum_range_succ] at ih ⊢
    rw [prefix_succ]
    simp only [squares, sum_range_succ]
    have hs : (∑ i ∈ range m, p i * p m * 1) = prefixMass p m * p m := by
      simp [prefixMass, sum_mul]
    rw [hs]
    simp only [squares] at ih
    nlinarith

private theorem pair_companions (p f : ℕ → ℝ) (m : ℕ) :
    (∑ j ∈ range m, ∑ i ∈ range j, p i * p j * (f i + f j)) =
      ∑ i ∈ range m, p i * f i * (prefixMass p m - p i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ, prefix_succ]
    have hi : (∑ i ∈ range m, p i * f i * (prefixMass p m + p m - p i)) =
        (∑ i ∈ range m, p i * f i * (prefixMass p m - p i)) +
          p m * (∑ i ∈ range m, p i * f i) := by
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl; intro i _; ring
    have hj : (∑ i ∈ range m, p i * p m * (f i + f m)) =
        p m * (∑ i ∈ range m, p i * f i) + p m * f m * prefixMass p m := by
      simp only [prefixMass, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl; intro i _; ring
    rw [hi, hj]; ring

private theorem cell_eta {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u ≤ 1) :
    (u - l) * eta u ≤ ∫ t in l..u, eta t := by
  have h := integral_mono_on (μ := MeasureTheory.volume) hlu
    (continuous_const.intervalIntegrable _ _)
    (continuous_eta.intervalIntegrable _ _) (fun t ht => eta_antitone (hl.trans ht.1) ht.2 hu)
  simpa using h

private theorem cell_moment {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u ≤ 1) :
    (∫ t in l..u, t ^ 2 * eta t) ≤
      (u - l) * l ^ 2 * eta u + (eta 0 + slope/2) * (u - l) ^ 2 := by
  have hi := integral_mono_on (μ := MeasureTheory.volume) hlu
    ((by fun_prop : Continuous (fun t : ℝ => t ^ 2 * eta t)).intervalIntegrable _ _)
    ((by fun_prop : Continuous
      (fun t : ℝ => l ^ 2 * eta u + 2 * eta 0 * (t - l) + slope * (u - t))).intervalIntegrable _ _)
    ?_
  · have he : (∫ t in l..u, l ^ 2 * eta u + 2 * eta 0 * (t - l) + slope * (u - t)) =
        (u - l) * l ^ 2 * eta u + (eta 0 + slope/2) * (u - l) ^ 2 := by
      have hf : (fun t : ℝ => l ^ 2 * eta u + 2 * eta 0 * (t - l) + slope * (u - t)) =
          (fun t => (2 * eta 0 - slope) * t + (l ^ 2 * eta u - 2 * eta 0 * l + slope * u)) := by
        funext t; ring
      have hlin : IntervalIntegrable (fun t : ℝ => (2 * eta 0 - slope) * t)
          MeasureTheory.volume l u :=
        (continuous_const.mul continuous_id).intervalIntegrable _ _
      have hconst : IntervalIntegrable
          (fun _ : ℝ => l ^ 2 * eta u - 2 * eta 0 * l + slope * u)
          MeasureTheory.volume l u := continuous_const.intervalIntegrable _ _
      rw [hf, integral_add hlin hconst, integral_const_mul, integral_id, integral_const]
      simp only [smul_eq_mul]
      ring
    rwa [he] at hi
  · intro t ht
    have ht0 := hl.trans ht.1
    have ht1 := ht.2.trans hu
    have hteta := eta_antitone (show (0:ℝ) ≤ 0 by norm_num) ht0 ht1
    have hd := eta_difference ht0 ht.2 hu
    have he0 := eta_nonneg (show (0:ℝ) ≤ 1 by norm_num)
    have het := eta_nonneg ht1
    have hsq : t ^ 2 - l ^ 2 ≤ 2 * (t - l) := by
      have hf : 0 ≤ 2 - t - l := by linarith [ht.1, ht.2]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.1) hf]
    have hsq0 : 0 ≤ t ^ 2 - l ^ 2 := sub_nonneg.mpr (pow_le_pow_left₀ hl ht.1 2)
    have hl1 : l ^ 2 ≤ 1 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hsq he0
    have h2 := mul_le_mul_of_nonneg_left hteta hsq0
    have h3 := mul_le_mul_of_nonneg_left hd (sq_nonneg l)
    have h4 := mul_le_mul_of_nonneg_right hl1
      (mul_nonneg (by norm_num [slope] : 0 ≤ slope) (sub_nonneg.mpr ht.2))
    nlinarith

private theorem weighted_edges {p : ℕ → ℝ} {d : ℕ → ℕ → ℝ} {n : ℕ}
    (hp : ∀ i < n, 0 ≤ p i) (hmass : prefixMass p n = 1)
    (hd : ∀ i j, i < j → j < n → 0 ≤ d i j) :
    weightedTriples p (fun i j k => w * d i j + d i k + d j k) n ≤ 2 * pairs p d n := by
  have dp : ∀ m ≤ n, 0 ≤ pairs p d m := by
    intro m hm
    apply sum_nonneg; intro j hj
    apply sum_nonneg; intro i hi
    have hjn := lt_of_lt_of_le (mem_range.mp hj) hm
    exact mul_nonneg (mul_nonneg (hp i (lt_trans (mem_range.mp hi) hjn)) (hp j hjn))
      (hd i j (mem_range.mp hi) hjn)
  have inv : ∀ m ≤ n,
      weightedTriples p (fun i j k => w * d i j + d i k + d j k) m ≤
        2 * (1 - w * (∫ t in prefixMass p m..1, eta t)) * pairs p d m := by
    intro m hm
    induction m with
    | zero => simp [weightedTriples, pairs]
    | succ m ih =>
      have hmn : m < n := lt_of_lt_of_le (Nat.lt_succ_self _) hm
      have hmle : m ≤ n := Nat.le_of_lt hmn
      have pm := hp m hmn
      have l0 := prefix_nonneg hp hmle
      have u1 := prefix_le_one hp hmass hm
      have lu := prefix_mono hp (Nat.le_succ m) hm
      have eu0 := eta_nonneg u1
      have wb : 0 ≤ w := by norm_num [w]
      have hc := cell_eta l0 lu u1
      have hc' : p m * eta (prefixMass p (m + 1)) ≤
          ∫ t in prefixMass p m..prefixMass p (m + 1), eta t := by
        simpa only [prefix_succ, add_sub_cancel_left] using hc
      have ht : (∫ t in prefixMass p m..1, eta t) =
          (∫ t in prefixMass p m..prefixMass p (m + 1), eta t) +
            (∫ t in prefixMass p (m + 1)..1, eta t) := by
        exact (integral_add_adjacent_intervals (continuous_eta.intervalIntegrable _ _)
          (continuous_eta.intervalIntegrable _ _)).symm
      have hcoef : (1 - w * (∫ t in prefixMass p m..1, eta t)) +
          w * p m * eta (prefixMass p (m + 1)) ≤
            1 - w * (∫ t in prefixMass p (m + 1)..1, eta t) := by
        rw [ht]; nlinarith [mul_le_mul_of_nonneg_left hc' wb]
      have hcomp : eta (prefixMass p (m + 1)) *
          (∑ i ∈ range m, p i * d i m * (prefixMass p m - p i)) ≤
          (1 - w * (∫ t in prefixMass p (m + 1)..1, eta t)) *
            (∑ i ∈ range m, p i * d i m) := by
        simp only [mul_sum]
        apply sum_le_sum; intro i hi
        have pin := hp i (lt_trans (mem_range.mp hi) hmn)
        have din := hd i m (mem_range.mp hi) hmn
        have hbudget := eta_budget u1
        have hlow : prefixMass p m - p i ≤ prefixMass p (m + 1) := by rw [prefix_succ]; linarith
        have hfactor : eta (prefixMass p (m + 1)) * (prefixMass p m - p i) ≤
            1 - w * (∫ t in prefixMass p (m + 1)..1, eta t) := by
          nlinarith [mul_le_mul_of_nonneg_left hlow eu0]
        convert mul_le_mul_of_nonneg_left hfactor (mul_nonneg pin din) using 1 <;> ring
      have hshell : (∑ j ∈ range m, ∑ i ∈ range j,
          2 * p i * p j * p m * (w * d i j + d i m + d j m)) =
            2 * p m * (w * pairs p d m +
              ∑ i ∈ range m, p i * d i m * (prefixMass p m - p i)) := by
        rw [← pair_companions]
        simp only [pairs, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl; intro j _
        apply sum_congr rfl; intro i _; ring
      have hnew : pairs p d (m + 1) =
          pairs p d m + p m * (∑ i ∈ range m, p i * d i m) := by
        simp only [pairs, sum_range_succ, mul_sum]
        congr 1; apply sum_congr rfl; intro i _; ring
      have hstep : weightedTriples p (fun i j k => w * d i j + d i k + d j k) (m + 1) =
          weightedTriples p (fun i j k => w * d i j + d i k + d j k) m +
            eta (prefixMass p (m + 1)) * (2 * p m * (w * pairs p d m +
              ∑ i ∈ range m, p i * d i m * (prefixMass p m - p i))) := by
        simp only [weightedTriples, sum_range_succ]; rw [hshell]
      rw [hstep, hnew]
      have h1 := mul_le_mul_of_nonneg_right hcoef (dp m hmle)
      have h2 := mul_le_mul_of_nonneg_left hcomp (by positivity : 0 ≤ 2 * p m)
      have h3 := ih hmle
      nlinarith
  have h := inv n le_rfl
  simpa only [hmass, integral_same, mul_zero, sub_zero, mul_one] using h

/-- Distinct sorted triples retain the second moment, up to the stated atom correction. -/
theorem weighted_mass {p : ℕ → ℝ} {n : ℕ}
    (hp : ∀ i < n, 0 ≤ p i) (hmass : prefixMass p n = 1) :
    I - K * squares p n ≤ weightedTriples p (fun _ _ _ => 1) n := by
  have heq : weightedTriples p (fun _ _ _ => 1) n =
      (∑ k ∈ range n, p k * (prefixMass p k) ^ 2 * eta (prefixMass p (k + 1))) -
        ∑ k ∈ range n, p k * eta (prefixMass p (k + 1)) * squares p k := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl; intro k _
    have hs : (∑ j ∈ range k, ∑ i ∈ range j, 2 * p i * p j * p k * 1) =
        p k * (2 * pairs p (fun _ _ => 1) k) := by
      simp only [pairs, mul_sum]
      apply sum_congr rfl; intro j _
      apply sum_congr rfl; intro i _; ring
    change eta (prefixMass p (k + 1)) * _ = _
    rw [hs, pair_constant]; ring
  have hquad : I ≤ (∑ k ∈ range n, p k * (prefixMass p k) ^ 2 * eta (prefixMass p (k + 1))) +
      (eta 0 + slope/2) * squares p n := by
    have hs := sum_le_sum (s := range n) (fun k hk =>
      cell_moment (prefix_nonneg hp (Nat.le_of_lt (mem_range.mp hk)))
        (prefix_mono hp (Nat.le_succ k) (Nat.succ_le_of_lt (mem_range.mp hk)))
        (prefix_le_one hp hmass (Nat.succ_le_of_lt (mem_range.mp hk))))
    rw [sum_integral_adjacent_intervals (fun k _ =>
      ((by fun_prop : Continuous (fun t : ℝ => t ^ 2 * eta t)).intervalIntegrable _ _)),
      prefix_zero, hmass, integral_moment_unit] at hs
    convert hs using 1
    simp only [prefix_succ, add_sub_cancel_left, sum_add_distrib, squares, mul_sum]
  have hrep : (∑ k ∈ range n, p k * eta (prefixMass p (k + 1)) * squares p k) ≤
      eta 0 * squares p n := by
    calc
      _ ≤ ∑ k ∈ range n, p k * (eta 0 * squares p n) := by
        apply sum_le_sum; intro k hk
        have pk := hp k (mem_range.mp hk)
        have hk1 := prefix_le_one hp hmass (Nat.succ_le_of_lt (mem_range.mp hk))
        have hk0 := prefix_nonneg hp (Nat.succ_le_of_lt (mem_range.mp hk))
        have he := eta_antitone (by norm_num : (0:ℝ) ≤ 0) hk0 hk1
        have he0 := eta_nonneg hk1
        have hs0 : 0 ≤ squares p k := sum_nonneg (fun i _ => sq_nonneg (p i))
        have hs := squares_mono p (Nat.le_of_lt (mem_range.mp hk))
        have hmul := mul_le_mul he hs hs0 (eta_nonneg (by norm_num : (0:ℝ) ≤ 1))
        convert mul_le_mul_of_nonneg_left hmul pk using 1; ring
      _ = eta 0 * squares p n := by rw [← sum_mul, ← prefixMass, hmass, one_mul]
  rw [heq, K_eq]; nlinarith

private theorem summation_by_parts (a b : ℕ → ℝ) (n : ℕ) (hb : b 0 = 0) :
    (∑ k ∈ range n, a k * (b (k + 1) - b k)) =
      a n * b n + ∑ k ∈ range n, (a k - a (k + 1)) * b (k + 1) := by
  induction n with
  | zero => simp [hb]
  | succ n ih => rw [sum_range_succ, ih, sum_range_succ]; ring

/-- Prefix control of sorted square sums implies its polynomially weighted form. -/
theorem weighted_curl {p : ℕ → ℝ} {h : ℕ → ℕ → ℕ → ℝ} {n : ℕ} {H : ℝ}
    (hp : ∀ i < n, 0 ≤ p i) (hmass : prefixMass p n = 1) (hH : 0 ≤ H)
    (hprefix : ∀ m ≤ n, triples p h m ≤ prefixMass p m * H) :
    weightedTriples p h n ≤ I0 * H := by
  let a : ℕ → ℝ := fun k => eta (prefixMass p (min (k + 1) n))
  have an : a n = 1 := by simp [a, hmass, eta_one]
  have ha : ∀ k < n, 0 ≤ a k - a (k + 1) := by
    intro k hk
    apply sub_nonneg.mpr
    apply eta_antitone (prefix_nonneg hp (Nat.min_le_right _ _))
      (prefix_mono hp (min_le_min_right n (Nat.le_succ (k + 1))) (Nat.min_le_right _ _))
      (prefix_le_one hp hmass (Nat.min_le_right _ _))
  have hc : weightedTriples p h n = ∑ k ∈ range n,
      a k * (triples p h (k + 1) - triples p h k) := by
    apply sum_congr rfl; intro k hk
    simp only [triples, sum_range_succ, add_sub_cancel_left]
    rw [show a k = eta (prefixMass p (k + 1)) by
      simp only [a, Nat.min_eq_left (Nat.succ_le_of_lt (mem_range.mp hk))]]
  have hp0 : prefixMass p 0 * H = 0 := by simp
  have ht0 : triples p h 0 = 0 := by simp [triples]
  have hdom : weightedTriples p h n ≤
      ∑ k ∈ range n, a k * (prefixMass p (k + 1) * H - prefixMass p k * H) := by
    rw [hc, summation_by_parts a (triples p h) n ht0,
      summation_by_parts a (fun k => prefixMass p k * H) n hp0, an, one_mul, one_mul]
    apply add_le_add (hprefix n le_rfl)
    apply sum_le_sum; intro k hk
    exact mul_le_mul_of_nonneg_left
      (hprefix (k + 1) (Nat.succ_le_of_lt (mem_range.mp hk))) (ha k (mem_range.mp hk))
  have hs : (∑ k ∈ range n, p k * eta (prefixMass p (k + 1))) ≤ I0 := by
    have hh := sum_le_sum (s := range n) (fun k hk =>
      cell_eta (prefix_nonneg hp (Nat.le_of_lt (mem_range.mp hk)))
        (prefix_mono hp (Nat.le_succ k) (Nat.succ_le_of_lt (mem_range.mp hk)))
        (prefix_le_one hp hmass (Nat.succ_le_of_lt (mem_range.mp hk))))
    rw [sum_integral_adjacent_intervals (fun k _ => (continuous_eta.intervalIntegrable _ _)),
      prefix_zero, hmass, integral_eta_unit] at hh
    simpa only [prefix_succ, add_sub_cancel_left] using hh
  have heq : (∑ k ∈ range n, a k * (prefixMass p (k + 1) * H - prefixMass p k * H)) =
      (∑ k ∈ range n, p k * eta (prefixMass p (k + 1))) * H := by
    rw [sum_mul]; apply sum_congr rfl; intro k hk
    simp only [a, Nat.min_eq_left (Nat.succ_le_of_lt (mem_range.mp hk)), prefix_succ]
    ring
  rw [heq] at hdom
  exact hdom.trans (mul_le_mul_of_nonneg_right hs hH)

/-- Equation (13), from the quadratic triangle inequality and abstract prefixMass curl control.
The square variable can be the curl norm square: its coefficientwise alignment bound
has already been absorbed into the displayed triangle hypothesis. -/
theorem flat_triangle_deficit {p : ℕ → ℝ} {d : ℕ → ℕ → ℝ}
    {h : ℕ → ℕ → ℕ → ℝ} {n : ℕ} {H : ℝ}
    (hp : ∀ i < n, 0 ≤ p i) (hmass : prefixMass p n = 1)
    (hd : ∀ i j, i < j → j < n → 0 ≤ d i j) (hH : 0 ≤ H)
    (htriangle : ∀ i j k, i < j → j < k → k < n →
      c - gamma * h i j k ≤ w * d i j + d i k + d j k)
    (hprefix : ∀ m ≤ n, triples p h m ≤ prefixMass p m * H) :
    c * I - c * K * squares p n - gamma * I0 * H ≤ 2 * pairs p d n := by
  have hlocal : c * weightedTriples p (fun _ _ _ => 1) n - gamma * weightedTriples p h n ≤
      weightedTriples p (fun i j k => w * d i j + d i k + d j k) n := by
    simp only [weightedTriples, mul_sum, ← sum_sub_distrib]
    apply sum_le_sum; intro k hk
    have ek := eta_nonneg (prefix_le_one hp hmass (Nat.succ_le_of_lt (mem_range.mp hk)))
    apply sum_le_sum; intro j hj
    apply sum_le_sum; intro i hi
    have hi0 := hp i (lt_trans (mem_range.mp hi) (lt_trans (mem_range.mp hj) (mem_range.mp hk)))
    have hj0 := hp j (lt_trans (mem_range.mp hj) (mem_range.mp hk))
    have hk0 := hp k (mem_range.mp hk)
    have hh := mul_le_mul_of_nonneg_left
      (htriangle i j k (mem_range.mp hi) (mem_range.mp hj) (mem_range.mp hk))
      (mul_nonneg ek (by positivity : 0 ≤ 2 * p i * p j * p k))
    convert hh using 1 <;> ring
  have hm := weighted_mass hp hmass
  have hc := weighted_curl hp hmass hH hprefix
  have he := weighted_edges hp hmass hd
  have cm : 0 ≤ c := by norm_num [c]
  have gm : 0 ≤ gamma := by norm_num [gamma]
  have h1 := mul_le_mul_of_nonneg_left hm cm
  have h2 := mul_le_mul_of_nonneg_left hc gm
  nlinarith

end HilbertPrefixDeficit
