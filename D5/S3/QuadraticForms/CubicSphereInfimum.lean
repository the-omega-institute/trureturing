/- GID: D5/S3/QuadraticForms/CubicSphereInfimum
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/CubicSphereInfimum
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Basic]
   utility: none
   digest: For h(t) = (3t - t³)/2 the infimum of R_h(x)² over unit vectors is 16(17 - 9√3)/23, never attained; two coordinates give 80/81. -/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! For the cubic `h(t) = (3t - t³)/2` and `R_h(x) = Σ xᵢ h(xᵢ) / (Σ h(xᵢ)²)^{1/2}` on unit
vectors of every finite dimension: `h` is strictly increasing on `[-1, 1]` with `h(1) = 1` and
`h(t)/t` strictly decreasing on `t > 0`; the moment identity
`R_h(x)² = (3 - s₂)²/(9 - 6 s₂ + s₃)` with `sₖ = Σ (xᵢ²)ᵏ`; the infimum `16(17 - 9√3)/23` of
`R_h(x)²` over nonnegative unit vectors, with `16(17 - 9√3)/23 < R_h(x)²` for every unit
vector of any signs, approached by one squared coordinate `6 - 3√3` and `m` equal tail
coordinates; the bound `80/81 ≤ R_h(x)²` for unit vectors with at most two nonzero
coordinates, attained by a nonnegative vector in dimension two; and the squared-coordinate example `(4/5, 1/10, 1/10)` with value `13689/13885 < 80/81`.

admission_basis: escape-witness. Escape witnesses: moment (the moment identity on the sphere),
key_poly with lower_strict (the factorization `23(3 - a²)² - 16(17 - 9√3)(9 - 6a² + a³) =
(a - a*)² q(a)` with `q > 0` on `a ≥ 0`, the bound `s₃ ≤ √s₂ · s₂`, and the equality analysis forcing
every positive squared coordinate to equal `√s₂ = 1`), two_gap with two_lower (the identity
`R² - 80/81 = (9 s₂ - 7)²/(81(9 - 6 s₂ + s₃))` when `2 s₃ = 3 s₂ - 1`, which holds on two-point
supports), approach_tendsto (the limit of the diffuse-tail sequence). -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.QuadraticForms.CubicSphereInfimum


/-- The cubic `h(t) = (3t - t³)/2`. -/
def cubic (t : ℝ) : ℝ := (3 * t - t ^ 3) / 2

/-- The ratio `R_h(x) = (Σ xᵢ h(xᵢ)) / (Σ h(xᵢ)²)^{1/2}` for the cubic `h`. -/
def rayleigh {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  (∑ i, x i * cubic (x i)) / Real.sqrt (∑ i, cubic (x i) ^ 2)

/-- The infimum value `16(17 - 9√3)/23`. -/
def infimumValue : ℝ := 16 * (17 - 9 * Real.sqrt 3) / 23

/-- The large squared coordinate `a* = 6 - 3√3` of the minimizing sequence. -/
def largeMass : ℝ := 6 - 3 * Real.sqrt 3

private theorem sqrt3_bounds : 1.73 < Real.sqrt 3 ∧ Real.sqrt 3 < 1.7321 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

private theorem moment_num {d : ℕ} (x : Fin d → ℝ) (hs : ∑ i, x i ^ 2 = 1) :
    ∑ i, x i * cubic (x i) = (3 - ∑ i, (x i ^ 2) ^ 2) / 2 := by
  have : ∀ i, x i * cubic (x i) = (3 * x i ^ 2 - (x i ^ 2) ^ 2) / 2 := fun i => by unfold cubic; ring
  simp only [this, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hs]
  ring

private theorem moment_den {d : ℕ} (x : Fin d → ℝ) (hs : ∑ i, x i ^ 2 = 1) :
    ∑ i, cubic (x i) ^ 2 = (9 - 6 * ∑ i, (x i ^ 2) ^ 2 + ∑ i, (x i ^ 2) ^ 3) / 4 := by
  have : ∀ i, cubic (x i) ^ 2 = (9 * x i ^ 2 - 6 * (x i ^ 2) ^ 2 + (x i ^ 2) ^ 3) / 4 :=
    fun i => by unfold cubic; ring
  simp only [this, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hs]
  ring

/-- The moment identity (5). -/
theorem moment {d : ℕ} (x : Fin d → ℝ) (hs : ∑ i, x i ^ 2 = 1) :
    rayleigh x ^ 2 = (3 - ∑ i, (x i ^ 2) ^ 2) ^ 2 /
      (9 - 6 * ∑ i, (x i ^ 2) ^ 2 + ∑ i, (x i ^ 2) ^ 3) := by
  unfold rayleigh
  rw [div_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  rw [moment_num x hs, moment_den x hs]
  field_simp
  ring

/-- `f(a) ≥ infimumValue` on `a ≥ 0`, via `(a - a*)² · q(a)`. -/
private theorem key_poly (a : ℝ) :
    23 * (3 - a ^ 2) ^ 2 - 16 * (17 - 9 * Real.sqrt 3) * (9 - 6 * a ^ 2 + a ^ 3) =
      (a - largeMass) ^ 2 * (23 * a ^ 2 + (4 + 6 * Real.sqrt 3) * a + (12 * Real.sqrt 3 - 15)) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold largeMass
  ring_nf
  rw [show Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 by ring, h3]
  ring_nf


private theorem q_pos (a : ℝ) (ha : 0 ≤ a) :
    0 < 23 * a ^ 2 + (4 + 6 * Real.sqrt 3) * a + (12 * Real.sqrt 3 - 15) := by
  have := sqrt3_bounds.1
  have : 0 ≤ (4 + 6 * Real.sqrt 3) * a := mul_nonneg (by linarith) ha
  nlinarith [sq_nonneg a]

private theorem largeMass_lt_one : largeMass < 1 := by unfold largeMass; linarith [sqrt3_bounds.1]
private theorem largeMass_pos : 0 < largeMass := by unfold largeMass; linarith [sqrt3_bounds.2]

private theorem infimumValue_pos : 0 < infimumValue := by unfold infimumValue; linarith [sqrt3_bounds.2]

/-- Strict lower bound: `infimumValue < R_h(x)²` for every unit vector, of any signs. -/
private theorem lower_strict {d : ℕ} (x : Fin d → ℝ) (hs : ∑ i, x i ^ 2 = 1) :
    infimumValue < rayleigh x ^ 2 := by
  set p : Fin d → ℝ := fun i => x i ^ 2 with hp
  have hp0 : ∀ i, 0 ≤ p i := fun i => by positivity
  have hpsum : ∑ i, p i = 1 := hs
  have hp1 : ∀ i, p i ≤ 1 := fun i => by
    rw [← hpsum]; exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
  set s2 := ∑ i, p i ^ 2 with hs2
  set s3 := ∑ i, p i ^ 3 with hs3
  have hs2le : s2 ≤ 1 := by
    rw [← hpsum]; exact Finset.sum_le_sum fun i _ => by nlinarith [hp0 i, hp1 i]
  have hs2pos : 0 < s2 := by
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hpsum]; norm_num :
      ∑ i, p i ≠ 0)
    have : 0 < p i ^ 2 := by positivity
    exact lt_of_lt_of_le this (Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i))
  set a := Real.sqrt s2 with ha
  have ha0 : 0 < a := Real.sqrt_pos.mpr hs2pos
  have ha2 : a ^ 2 = s2 := Real.sq_sqrt hs2pos.le
  have ha1 : a ≤ 1 := by rw [ha, Real.sqrt_le_one]; exact hs2le
  have hpa : ∀ i, p i ≤ a := fun i => by
    rw [ha, Real.le_sqrt (hp0 i) hs2pos.le]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
  have hs3le : s3 ≤ a * s2 := by
    rw [hs3, hs2, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      have := mul_le_mul_of_nonneg_left (hpa i) (sq_nonneg (p i)); nlinarith [this]
  have hs3nn : 0 ≤ s3 := Finset.sum_nonneg fun i _ => pow_nonneg (hp0 i) 3
  have hR : rayleigh x ^ 2 = (3 - s2) ^ 2 / (9 - 6 * s2 + s3) := moment x hs
  have hD : 0 < 9 - 6 * s2 + s3 := by linarith
  rw [hR, lt_div_iff₀ hD]
  have hkey := key_poly a
  have hq := q_pos a ha0.le
  rw [ha2] at hkey
  have hc : infimumValue = 16 * (17 - 9 * Real.sqrt 3) / 23 := rfl
  have hcp := infimumValue_pos
  rcases lt_or_eq_of_le hs3le with hlt | heq
  · -- strict in the denominator
    have h1 : infimumValue * (9 - 6 * s2 + s3) < infimumValue * (9 - 6 * s2 + a * s2) :=
      mul_lt_mul_of_pos_left (by linarith) hcp
    have h2 : infimumValue * (9 - 6 * s2 + a * s2) ≤ (3 - s2) ^ 2 := by
      have : a * s2 = a ^ 3 := by rw [← ha2]; ring
      rw [this, hc]
      nlinarith [mul_nonneg (sq_nonneg (a - largeMass)) hq.le]
    linarith
  · -- equality s3 = a s2 forces every p i ∈ {0, a}, hence a = 1
    have hterm : ∀ i, p i ^ 2 * (a - p i) = 0 := by
      have hsum0 : ∑ i, p i ^ 2 * (a - p i) = 0 := by
        have : ∑ i, p i ^ 2 * (a - p i) = a * s2 - s3 := by
          rw [hs2, hs3, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [this, heq]; ring
      exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (hpa i))).mp hsum0 |> fun h i => h i (Finset.mem_univ i)
    have hlin : ∀ i, p i * (a - p i) = 0 := fun i => by
      rcases mul_eq_zero.mp (hterm i) with h | h
      · rw [pow_eq_zero_iff (by norm_num)] at h; rw [h]; ring
      · rw [h, mul_zero]
    have hsa : a * 1 - s2 = 0 := by
      have : ∑ i, p i * (a - p i) = a * ∑ i, p i - s2 := by
        rw [hs2, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [← hpsum, ← this]; exact Finset.sum_eq_zero fun i _ => hlin i
    have ha_one : a = 1 := by nlinarith
    have hne : (a - largeMass) ^ 2 > 0 := by
      have := largeMass_lt_one; rw [ha_one]; nlinarith
    have : 0 < (a - largeMass) ^ 2 * (23 * a ^ 2 + (4 + 6 * Real.sqrt 3) * a +
        (12 * Real.sqrt 3 - 15)) := mul_pos hne hq
    have h3 : a * s2 = a ^ 3 := by rw [← ha2]; ring
    rw [← heq, h3] at *
    rw [hc]
    nlinarith


/-- Moment form with an `s₃ = (3 s₂ - 1)/2` relation gives `80/81 ≤ R²` with the exact gap. -/
private theorem two_gap (s2 s3 : ℝ) (hrel : 2 * s3 = 3 * s2 - 1) (hs2 : s2 ≤ 1) :
    (3 - s2) ^ 2 / (9 - 6 * s2 + s3) - 80 / 81 = (9 * s2 - 7) ^ 2 / (81 * (9 - 6 * s2 + s3)) := by
  have hD : 0 < 9 - 6 * s2 + s3 := by linarith
  rw [div_sub_div _ _ hD.ne' (by norm_num : (81:ℝ) ≠ 0), mul_comm (9 - 6 * s2 + s3) 81]
  congr 1
  linear_combination (-40) * hrel

private theorem sum_support_pair {d : ℕ} (x : Fin d → ℝ) (j k : Fin d)
    (hjk : ∀ i, x i ≠ 0 → i = j ∨ i = k) (F : ℝ → ℝ) (hF : F 0 = 0) :
    ∑ i, F (x i) = ∑ i ∈ ({j, k} : Finset (Fin d)), F (x i) := by
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
  have : x i = 0 := by
    by_contra h
    rcases hjk i h with rfl | rfl <;> simp at hi
  rw [this, hF]

/-- With at most two nonzero coordinates, `80/81 ≤ R_h(x)²`. -/
private theorem two_lower {d : ℕ} (x : Fin d → ℝ) (hs : ∑ i, x i ^ 2 = 1)
    (j k : Fin d) (hjk : ∀ i, x i ≠ 0 → i = j ∨ i = k) :
    80 / 81 ≤ rayleigh x ^ 2 := by
  set p : Fin d → ℝ := fun i => x i ^ 2
  have hp0 : ∀ i, 0 ≤ p i := fun i => sq_nonneg _
  have e1 := sum_support_pair x j k hjk (fun t => t ^ 2) (by norm_num)
  have e2 := sum_support_pair x j k hjk (fun t => (t ^ 2) ^ 2) (by norm_num)
  have e3 := sum_support_pair x j k hjk (fun t => (t ^ 2) ^ 3) (by norm_num)
  have hrel : 2 * ∑ i, p i ^ 3 = 3 * ∑ i, p i ^ 2 - 1 := by
    show 2 * ∑ i, (x i ^ 2) ^ 3 = 3 * ∑ i, (x i ^ 2) ^ 2 - 1
    rw [e2, e3]; rw [e1] at hs
    by_cases h : j = k
    · subst h
      have hjj : ({j, j} : Finset (Fin d)) = {j} := by simp
      rw [hjj, Finset.sum_singleton] at hs ⊢; rw [Finset.sum_singleton, hs]; norm_num
    · rw [Finset.sum_pair h] at hs ⊢; rw [Finset.sum_pair h]
      have hb : x k ^ 2 = 1 - x j ^ 2 := by linarith
      rw [hb]; ring
  have hs2 : ∑ i, p i ^ 2 ≤ 1 := by
    have hpsum : ∑ i, p i = 1 := hs
    rw [← hpsum]; refine Finset.sum_le_sum fun i _ => ?_
    have : p i ≤ 1 := by
      rw [← hpsum]; exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
    nlinarith [hp0 i]
  have hD : 0 < 9 - 6 * ∑ i, p i ^ 2 + ∑ i, p i ^ 3 := by linarith
  have hg := two_gap _ _ hrel hs2
  rw [moment x hs]
  have : 0 ≤ (9 * ∑ i, p i ^ 2 - 7) ^ 2 / (81 * (9 - 6 * ∑ i, p i ^ 2 + ∑ i, p i ^ 3)) :=
    div_nonneg (sq_nonneg _) (by positivity)
  linarith

/-- The two-coordinate minimum `80/81` is attained. -/
private theorem two_attained : ∃ x : Fin 2 → ℝ, (∀ i, 0 ≤ x i) ∧ ∑ i, x i ^ 2 = 1 ∧ rayleigh x ^ 2 = 80 / 81 := by
  set p : ℝ := (3 + Real.sqrt 5) / 6
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5a : Real.sqrt 5 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h5b : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hp0 : 0 ≤ p := by positivity
  have hp1 : 0 ≤ 1 - p := by simp only [p]; linarith
  refine ⟨![Real.sqrt p, Real.sqrt (1 - p)], fun i => by fin_cases i <;> simp [Real.sqrt_nonneg],
    ?_, ?_⟩
  · simp [Fin.sum_univ_two, Real.sq_sqrt hp0, Real.sq_sqrt hp1]
  · have hs : ∑ i, (![Real.sqrt p, Real.sqrt (1 - p)] : Fin 2 → ℝ) i ^ 2 = 1 := by
      simp [Fin.sum_univ_two, Real.sq_sqrt hp0, Real.sq_sqrt hp1]
    rw [moment _ hs]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.sq_sqrt hp0, Real.sq_sqrt hp1]
    have hu : p * (1 - p) = 1 / 9 := by simp only [p]; linear_combination (-1/36) * h5
    have hD : 0 < 9 - 6 * (p ^ 2 + (1 - p) ^ 2) + (p ^ 3 + (1 - p) ^ 3) := by nlinarith
    rw [div_eq_iff hD.ne']
    linear_combination 4 * (p * (1 - p) - 1 / 9) * hu

/-- The squared-coordinate example `(4/5, 1/10, 1/10)`. -/
private theorem example_value :
    rayleigh (![Real.sqrt (4/5), Real.sqrt (1/10), Real.sqrt (1/10)] : Fin 3 → ℝ) ^ 2 = 13689 / 13885 := by
  have hs : ∑ i, (![Real.sqrt (4/5), Real.sqrt (1/10), Real.sqrt (1/10)] : Fin 3 → ℝ) i ^ 2 = 1 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Real.sq_sqrt (show (0:ℝ) ≤ 4/5 by norm_num),
      Real.sq_sqrt (show (0:ℝ) ≤ 1/10 by norm_num)]
    norm_num
  rw [moment _ hs]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Real.sq_sqrt (show (0:ℝ) ≤ 4/5 by norm_num),
    Real.sq_sqrt (show (0:ℝ) ≤ 1/10 by norm_num)]
  norm_num

private theorem example_lt : (13689 : ℝ) / 13885 < 80 / 81 := by norm_num

private theorem h_one : cubic 1 = 1 := by unfold cubic; norm_num

private theorem h_strictMonoOn : StrictMonoOn cubic (Set.Icc (-1) 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Icc] at ha hb
  have hq : (0:ℝ) < 3 - (a ^ 2 + a * b + b ^ 2) := by
    nlinarith [mul_pos (sub_pos.mpr hab) (sub_pos.mpr hab), mul_nonneg (sub_nonneg.mpr ha.2)
      (neg_le_iff_add_nonneg.mp ha.1), mul_nonneg (sub_nonneg.mpr hb.2) (neg_le_iff_add_nonneg.mp hb.1)]
  unfold cubic
  nlinarith [mul_pos (sub_pos.mpr hab) hq]

private theorem ratio_strictAntiOn : StrictAntiOn (fun t => cubic t / t) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have e : ∀ t : ℝ, 0 < t → cubic t / t = (3 - t ^ 2) / 2 := fun t ht => by
    unfold cubic; field_simp
  simp only
  rw [e a ha, e b hb]
  nlinarith


/-- One large squared coordinate `6 - 3√3` plus `m` equal tail coordinates. -/
def approach (m : ℕ) : Fin (m + 1) → ℝ :=
  Fin.cons (Real.sqrt largeMass) fun _ => Real.sqrt ((1 - largeMass) / m)

private theorem approach_nonneg (m : ℕ) (i : Fin (m + 1)) : 0 ≤ approach m i := by
  refine Fin.cases ?_ (fun _ => ?_) i <;>
    simp only [approach, Fin.cons_zero, Fin.cons_succ] <;> exact Real.sqrt_nonneg _

private theorem approach_sum (m : ℕ) (F : ℝ → ℝ) :
    ∑ i, F (approach m i ^ 2) = F largeMass + m * F ((1 - largeMass) / m) := by
  have h1 : 0 ≤ 1 - largeMass := by linarith [largeMass_lt_one]
  rw [Fin.sum_univ_succ]
  simp only [approach, Fin.cons_zero, Fin.cons_succ, Real.sq_sqrt largeMass_pos.le,
    Real.sq_sqrt (div_nonneg h1 (Nat.cast_nonneg m)), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

private theorem approach_unit (m : ℕ) (hm : 1 ≤ m) : ∑ i, approach m i ^ 2 = 1 := by
  have := approach_sum m id
  simp only [id] at this
  rw [this]; have : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  field_simp; ring

private theorem fstar : (3 - largeMass ^ 2) ^ 2 / (9 - 6 * largeMass ^ 2 + largeMass ^ 3) = infimumValue := by
  have hD : 0 < 9 - 6 * largeMass ^ 2 + largeMass ^ 3 := by
    have := largeMass_pos; have := largeMass_lt_one; nlinarith
  have hk : 23 * (3 - largeMass ^ 2) ^ 2 - 16 * (17 - 9 * Real.sqrt 3) *
      (9 - 6 * largeMass ^ 2 + largeMass ^ 3) = 0 := by rw [key_poly largeMass]; ring
  rw [div_eq_iff hD.ne']; unfold infimumValue; linarith

private theorem approach_tendsto :
    Filter.Tendsto (fun m => rayleigh (approach (m + 1)) ^ 2) Filter.atTop (nhds infimumValue) := by
  set c : ℝ := 1 - largeMass
  set g : ℝ → ℝ := fun u => (3 - (largeMass ^ 2 + c ^ 2 * u)) ^ 2 /
    (9 - 6 * (largeMass ^ 2 + c ^ 2 * u) + (largeMass ^ 3 + c ^ 3 * u ^ 2)) with hg
  have hR : ∀ m : ℕ, rayleigh (approach (m + 1)) ^ 2 = g (1 / ((m : ℝ) + 1)) := fun m => by
    have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
    rw [moment _ (approach_unit (m + 1) (by omega)), approach_sum (m + 1) (fun t => t ^ 2),
      approach_sum (m + 1) (fun t => t ^ 3)]
    simp only [hg, c]
    push_cast
    congr 1 <;> field_simp
  have hD : (9 - 6 * (largeMass ^ 2 + c ^ 2 * 0) + (largeMass ^ 3 + c ^ 3 * 0 ^ 2)) ≠ 0 := by
    have := largeMass_pos; have := largeMass_lt_one; nlinarith
  have hu : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have key : Filter.Tendsto (fun m : ℕ => g (1 / ((m : ℝ) + 1))) Filter.atTop (nhds (g 0)) := by
    simp only [hg]
    exact ((tendsto_const_nhds.sub (tendsto_const_nhds.add (tendsto_const_nhds.mul hu))).pow 2).div
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul (tendsto_const_nhds.add
        (tendsto_const_nhds.mul hu))) |>.add (tendsto_const_nhds.add
          (tendsto_const_nhds.mul (hu.pow 2)))) hD
  have hg0 : g 0 = infimumValue := by simp only [hg]; rw [← fstar]; ring_nf
  rw [← hg0]
  simpa only [hR] using key

/-- `infimumValue` is the greatest lower bound of `R_h(x)²` over nonnegative unit vectors of every
finite dimension. -/
private theorem infimum :
    IsGLB {r | ∃ (d : ℕ) (x : Fin d → ℝ), (∀ i, 0 ≤ x i) ∧ ∑ i, x i ^ 2 = 1 ∧
      rayleigh x ^ 2 = r} infimumValue := by
  refine ⟨?_, ?_⟩
  · rintro r ⟨d, x, -, hs, rfl⟩; exact (lower_strict x hs).le
  · intro b hb
    refine ge_of_tendsto approach_tendsto (Filter.Eventually.of_forall fun m => hb ?_)
    exact ⟨m + 1 + 1, approach (m + 1), approach_nonneg _, approach_unit _ (by omega), rfl⟩

/-- Theorem 11 of Ma–Zhang (DOI 10.5281/zenodo.23920598) for `h(t) = (3t - t³)/2`, with the
monotonicity of `h` on `[-1, 1]`, the decrease of `h(t)/t` on `t > 0`, and both lower bounds for
every unit vector of any sign. -/
theorem result :
    StrictMonoOn cubic (Set.Icc (-1) 1) ∧ cubic 1 = 1 ∧
      StrictAntiOn (fun t => cubic t / t) (Set.Ioi 0) ∧
      (∀ (d : ℕ) (x : Fin d → ℝ), ∑ i, x i ^ 2 = 1 → infimumValue < rayleigh x ^ 2) ∧
      IsGLB {r | ∃ (d : ℕ) (x : Fin d → ℝ), (∀ i, 0 ≤ x i) ∧ ∑ i, x i ^ 2 = 1 ∧
        rayleigh x ^ 2 = r} infimumValue ∧
      (∀ m : ℕ, 1 ≤ m → (∀ i, 0 ≤ approach m i) ∧ ∑ i, approach m i ^ 2 = 1) ∧
      Filter.Tendsto (fun m => rayleigh (approach (m + 1)) ^ 2) Filter.atTop
        (nhds infimumValue) ∧
      (∀ (d : ℕ) (x : Fin d → ℝ), ∑ i, x i ^ 2 = 1 →
        (∃ j k : Fin d, ∀ i, x i ≠ 0 → i = j ∨ i = k) → 80 / 81 ≤ rayleigh x ^ 2) ∧
      (∃ x : Fin 2 → ℝ, (∀ i, 0 ≤ x i) ∧ ∑ i, x i ^ 2 = 1 ∧ rayleigh x ^ 2 = 80 / 81) ∧
      rayleigh (![Real.sqrt (4/5), Real.sqrt (1/10), Real.sqrt (1/10)] : Fin 3 → ℝ) ^ 2 =
        13689 / 13885 ∧ (13689 : ℝ) / 13885 < 80 / 81 :=
  ⟨h_strictMonoOn, h_one, ratio_strictAntiOn, fun _ x hs => lower_strict x hs, infimum,
    fun m hm => ⟨approach_nonneg m, approach_unit m hm⟩, approach_tendsto,
    fun _ x hs ⟨j, k, hjk⟩ => two_lower x hs j k hjk, two_attained, example_value, example_lt⟩

end D5.S3.QuadraticForms.CubicSphereInfimum
