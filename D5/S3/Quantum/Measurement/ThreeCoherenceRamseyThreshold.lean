/- GID: D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The exact three-coherence Ramsey third-moment threshold. -/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The sharp three-coherence Ramsey threshold -/

public section

noncomputable section

open Complex Real MeasureTheory Finset
open scoped BigOperators

namespace D5.S3.Quantum.Measurement.ThreeCoherenceRamseyThreshold

/-- The probability of a rank-one Ramsey measurement with integer energy labels. -/
def signal {d : ℕ} (n : Fin d → ℤ) (χ ψ : Fin d → ℂ) (t : ℝ) : ℝ :=
  Complex.normSq (∑ j, star (χ j) * Complex.exp (-(n j : ℂ) * t * I) * ψ j)

/-- A finite probabilistic mixture of pure Ramsey signals. -/
def mixedSignal {d L : ℕ} (n : Fin d → ℤ) (χ : Fin d → ℂ)
    (ψ : Fin L → Fin d → ℂ) (w : Fin L → ℝ) (t : ℝ) : ℝ :=
  ∑ l, w l * signal n χ (ψ l) t

/-- The normalized integral of a power over one period. -/
def moment (q : ℕ) (p : ℝ → ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ t in (0)..(2 * π), p t ^ q

/-- The third moment divided by the square of the first moment. -/
def ratio3 (p : ℝ → ℝ) : ℝ := moment 3 p / moment 1 p ^ 2

/-- At most three coordinates are nonzero. -/
def IsThreeSparse {d : ℕ} (ψ : Fin d → ℂ) : Prop :=
  (Function.support ψ).ncard ≤ 3

/-- The squared amplitudes sum to one. -/
def IsUnitVector {d : ℕ} (ψ : Fin d → ℂ) : Prop :=
  ∑ j, Complex.normSq (ψ j) = 1

/-- All third-moment ratios from finite mixtures of unit three-sparse vectors. -/
def admissibleValues : Set ℝ :=
  {v | ∃ (d L : ℕ) (n : Fin d → ℤ) (χ : Fin d → ℂ)
      (ψ : Fin L → Fin d → ℂ) (w : Fin L → ℝ),
    IsUnitVector χ ∧ (∀ l, IsUnitVector (ψ l) ∧ IsThreeSparse (ψ l)) ∧
    (∀ l, 0 ≤ w l) ∧ (∑ l, w l) = 1 ∧
    0 < moment 1 (mixedSignal n χ ψ w) ∧ v = ratio3 (mixedSignal n χ ψ w)}

def thresholdN (r : ℝ) : ℝ := r ^ 6 + 30 * r ^ 4 + 90 * r ^ 2 + 20

def thresholdD (r : ℝ) : ℝ := (r + 2) ^ 2 * (r ^ 2 + 2) ^ 2

def thresholdP (r : ℝ) : ℝ :=
  r ^ 7 - 13 * r ^ 6 + 6 * r ^ 5 - 60 * r ^ 4 + 30 * r ^ 3 -
    30 * r ^ 2 + 140 * r - 20

/-- The isolated algebraic value is the greatest physically admissible ratio. -/
def claim : Prop := ∃ α : ℝ,
  6169 / 5000 < α ∧ α < 12339 / 10000 ∧ thresholdP α = 0 ∧
  IsGreatest admissibleValues (thresholdN α / thresholdD α)

private def character (k : ℤ) (t : ℝ) : ℂ := Complex.exp ((k : ℂ) * t * I)

private def trigPoly {ι : Type*} [Fintype ι] (n : ι → ℤ) (z : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ j, z j * character (n j) t

private def average (f : ℝ → ℂ) : ℂ := (1 / (2 * π)) * ∫ t in (0)..(2 * π), f t

private theorem character_continuous (k : ℤ) : Continuous (character k) := by
  unfold character
  fun_prop

private theorem character_mul_star (k m : ℤ) (t : ℝ) :
    character k t * star (character m t) = character (k - m) t := by
  simp only [character, Complex.star_def, ← Complex.exp_conj, map_mul, map_intCast,
    Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add, Int.cast_sub]
  congr 1
  ring

private theorem character_average (k : ℤ) :
    average (character k) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [average, character, Complex.ofReal_mul, Complex.ofReal_ofNat]
    field_simp
  · have hkcomplex : (k : ℂ) * I ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hk) Complex.I_ne_zero
    have harg : ((k : ℂ) * I) * ((2 * π : ℝ) : ℂ) = k * (2 * π * I) := by
      push_cast
      ring
    have hint : (∫ t in (0)..(2 * π), character k t) = 0 := by
      simp only [character, mul_right_comm (k : ℂ) _ I]
      rw [integral_exp_mul_complex hkcomplex, harg, Complex.exp_int_mul_two_pi_mul_I]
      simp
    simp [average, hint, hk]

private theorem average_sum {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ)
    (hf : ∀ i, Continuous (f i)) :
    average (fun t => ∑ i, f i t) = ∑ i, average (f i) := by
  simp only [average, intervalIntegral.integral_finsetSum
    (fun i _ => (hf i).intervalIntegrable _ _), Finset.mul_sum]

private theorem moment_one_formula {ι : Type*} [Fintype ι]
    (n : ι → ℤ) (z : ι → ℂ) :
    moment 1 (fun t => Complex.normSq (trigPoly n z t)) =
      ∑ i, ∑ j, if n i = n j then (z i * star (z j)).re else 0 := by
  classical
  have hpoint (t : ℝ) : (Complex.normSq (trigPoly n z t) : ℂ) =
      ∑ i, ∑ j, (z i * star (z j)) * character (n i - n j) t := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]
    simp only [trigPoly, map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul]
    change (z i * character (n i) t) * (star (z j) * star (character (n j) t)) = _
    rw [← character_mul_star]
    ring
  have hcast : (moment 1 (fun t => Complex.normSq (trigPoly n z t)) : ℂ) =
      ∑ i, ∑ j, if n i = n j then z i * star (z j) else 0 := by
    simp only [moment, pow_one, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat, ← intervalIntegral.integral_ofReal]
    change average (fun t => (Complex.normSq (trigPoly n z t) : ℂ)) = _
    simp_rw [hpoint]
    rw [average_sum _ (fun i => by
      apply continuous_finsetSum
      intro j _
      exact continuous_const.mul (character_continuous _))]
    apply Finset.sum_congr rfl
    intro i _
    rw [average_sum (fun j t => (z i * star (z j)) * character (n i - n j) t)
      (fun j => continuous_const.mul (character_continuous _))]
    apply Finset.sum_congr rfl
    intro j _
    change average (fun t => (z i * star (z j)) * character (n i - n j) t) = _
    unfold average
    rw [intervalIntegral.integral_const_mul]
    rw [mul_left_comm]
    change (z i * star (z j)) * average (character (n i - n j)) = _
    rw [character_average]
    by_cases hij : n i = n j <;> simp [hij, sub_eq_zero]
  simpa only [Complex.ofReal_re, Complex.re_sum, apply_ite Complex.re,
    Complex.zero_re] using congrArg Complex.re hcast

private theorem trigPoly_power {ι : Type*} [Fintype ι]
    (n : ι → ℤ) (z : ι → ℂ) (q : ℕ) (t : ℝ) :
    trigPoly n z t ^ q = trigPoly
      (fun τ : Fin q → ι => ∑ i, n (τ i)) (fun τ => ∏ i, z (τ i)) t := by
  classical
  simp only [trigPoly, Fintype.sum_pow, Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro τ _
  congr 1
  simp only [character, ← Complex.exp_sum, ← Finset.sum_mul, ← Int.cast_sum]

private theorem moment_formula {ι : Type*} [Fintype ι]
    (n : ι → ℤ) (z : ι → ℂ) (q : ℕ) :
    moment q (fun t => Complex.normSq (trigPoly n z t)) =
      ∑ τ : Fin q → ι, ∑ σ : Fin q → ι,
        if (∑ i, n (τ i)) = ∑ i, n (σ i)
        then ((∏ i, z (τ i)) * star (∏ i, z (σ i))).re else 0 := by
  have hpoint (t : ℝ) : Complex.normSq (trigPoly n z t) ^ q =
      Complex.normSq (trigPoly (fun τ : Fin q → ι => ∑ i, n (τ i))
        (fun τ => ∏ i, z (τ i)) t) := by
    rw [← map_pow, trigPoly_power]
  have heq : moment q (fun t => Complex.normSq (trigPoly n z t)) =
      moment 1 (fun t => Complex.normSq (trigPoly (fun τ : Fin q → ι => ∑ i, n (τ i))
        (fun τ => ∏ i, z (τ i)) t)) := by
    simp only [moment, pow_one, hpoint]
  rw [heq, moment_one_formula]

private theorem moment_abs_le {ι : Type*} [Fintype ι]
    (n : ι → ℤ) (z : ι → ℂ) (q : ℕ) :
    moment q (fun t => Complex.normSq (trigPoly n z t)) ≤
      moment q (fun t => Complex.normSq (trigPoly n (fun i => (‖z i‖ : ℂ)) t)) := by
  classical
  rw [moment_formula, moment_formula]
  apply Finset.sum_le_sum
  intro τ _
  apply Finset.sum_le_sum
  intro σ _
  split_ifs
  · calc
      _ ≤ ‖(∏ i, z (τ i)) * star (∏ i, z (σ i))‖ := Complex.re_le_norm _
      _ = _ := by simp [norm_prod, ← Complex.ofReal_prod, ← Complex.ofReal_mul]
  · rfl

private theorem moment_one_injective {ι : Type*} [Fintype ι]
    (n : ι → ℤ) (z : ι → ℂ) (hn : Function.Injective n) :
    moment 1 (fun t => Complex.normSq (trigPoly n z t)) = ∑ i, ‖z i‖ ^ 2 := by
  classical
  rw [moment_one_formula]
  simp only [hn.eq_iff, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private theorem root_exists : ∃ α : ℝ,
    6169 / 5000 < α ∧ α < 12339 / 10000 ∧ thresholdP α = 0 := by
  have hlow : 0 < thresholdP (6169 / 5000) := by norm_num [thresholdP]
  have hhigh : thresholdP (12339 / 10000) < 0 := by norm_num [thresholdP]
  have hcont : Continuous thresholdP := by unfold thresholdP; fun_prop
  obtain ⟨α, hα, hzero⟩ := intermediate_value_Icc'
    (by norm_num : (6169 / 5000 : ℝ) ≤ 12339 / 10000) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (thresholdP (12339 / 10000))
      (thresholdP (6169 / 5000)) from ⟨hhigh.le, hlow.le⟩)
  refine ⟨α, lt_of_le_of_ne hα.1 ?_, lt_of_le_of_ne hα.2 ?_, hzero⟩
  · intro h; subst α; linarith
  · intro h; subst α; linarith

private theorem denominator_positive (r : ℝ) (hr : 0 ≤ r) : 0 < thresholdD r := by
  unfold thresholdD
  positivity

private theorem threshold_bound (α : ℝ) (hl : 6169 / 5000 < α)
    (hh : α < 12339 / 10000) (hp : thresholdP α = 0) :
    5 / 4 < thresholdN α / thresholdD α ∧
    ∀ r : ℝ, 0 ≤ r → thresholdN r / thresholdD r ≤ thresholdN α / thresholdD α := by
  have ha : (123 / 100 : ℝ) < α := by linarith
  have hb : α < (31 / 25 : ℝ) := by linarith
  have hapos : 0 ≤ α := by linarith
  have hd := denominator_positive α hapos
  let T := thresholdN α / thresholdD α
  have hnlo : thresholdN (6169 / 5000) ≤ thresholdN α := by
    unfold thresholdN
    gcongr
  have hdhi : thresholdD α ≤ thresholdD (12339 / 10000) := by
    unfold thresholdD
    gcongr
  have hnum : (177 / 100 : ℝ) * thresholdD (12339 / 10000) <
      thresholdN (6169 / 5000) := by norm_num [thresholdN, thresholdD]
  have ht : (177 / 100 : ℝ) < T := by
    apply (lt_div_iff₀ hd).2
    linarith
  have hv : T * thresholdD α - thresholdN α = 0 := by
    dsimp [T]
    rw [div_mul_cancel₀ _ hd.ne', sub_self]
  have hs : (α + 2) * (α ^ 2 + 2) *
      (T * (6 * α ^ 5 + 20 * α ^ 4 + 32 * α ^ 3 + 48 * α ^ 2 + 40 * α + 16) -
        (6 * α ^ 5 + 120 * α ^ 3 + 180 * α)) = 0 := by
    unfold thresholdD thresholdN at hv
    unfold thresholdP at hp
    linear_combination (6 * α ^ 2 + 8 * α + 4) * hv - 4 * hp
  have hstat : T * (6 * α ^ 5 + 20 * α ^ 4 + 32 * α ^ 3 + 48 * α ^ 2 + 40 * α + 16) -
      (6 * α ^ 5 + 120 * α ^ 3 + 180 * α) = 0 :=
    (mul_eq_zero.mp hs).resolve_left (by positivity)
  have hq4 : 0 < T - 1 := by linarith
  have hq3 : 0 < 4 * T + 2 * α * (T - 1) := by positivity
  have hq2 : 0 < 8 * T - 30 + 8 * α * T + 3 * α ^ 2 * (T - 1) := by
    have hbound : 8 * (177 / 100 : ℝ) + 8 * (123 / 100) * (177 / 100) +
        3 * (123 / 100) ^ 2 * (77 / 100) ≤
        8 * T + 8 * α * T + 3 * α ^ 2 * (T - 1) := by
      gcongr; linarith
    linarith
  have hq1 : 0 < 16 * T + 16 * α * T - 60 * α +
      12 * α ^ 2 * T + 4 * α ^ 3 * (T - 1) := by
    have hbound : 16 * (177 / 100 : ℝ) + 16 * (123 / 100) * (177 / 100) +
        12 * (123 / 100) ^ 2 * (177 / 100) + 4 * (123 / 100) ^ 3 * (77 / 100) ≤
        16 * T + 16 * α * T + 12 * α ^ 2 * T + 4 * α ^ 3 * (T - 1) := by
      gcongr; linarith
    linarith
  have hq0 : 0 < 20 * T - 90 + 32 * α * T + (24 * T - 90) * α ^ 2 +
      16 * T * α ^ 3 + 5 * (T - 1) * α ^ 4 := by
    have hbound : 20 * (177 / 100 : ℝ) + 32 * (123 / 100) * (177 / 100) +
        24 * (177 / 100) * (123 / 100) ^ 2 + 16 * (177 / 100) * (123 / 100) ^ 3 +
        5 * (77 / 100) * (123 / 100) ^ 4 ≤
        20 * T + 32 * α * T + 24 * T * α ^ 2 + 16 * T * α ^ 3 +
        5 * (T - 1) * α ^ 4 := by
      gcongr; linarith
    have hsquare : α ^ 2 ≤ (31 / 25 : ℝ) ^ 2 := by gcongr
    nlinarith only [hbound, hsquare]
  refine ⟨by dsimp [T] at ht; linarith, ?_⟩
  intro r hr
  have hidentity : T * thresholdD r - thresholdN r = (r - α) ^ 2 *
      ((T - 1) * r ^ 4 + (4 * T + 2 * α * (T - 1)) * r ^ 3 +
       (8 * T - 30 + 8 * α * T + 3 * α ^ 2 * (T - 1)) * r ^ 2 +
       (16 * T + 16 * α * T - 60 * α + 12 * α ^ 2 * T +
         4 * α ^ 3 * (T - 1)) * r +
       (20 * T - 90 + 32 * α * T + (24 * T - 90) * α ^ 2 +
         16 * T * α ^ 3 + 5 * (T - 1) * α ^ 4)) := by
    unfold thresholdD thresholdN at hv ⊢
    linear_combination hv + (r - α) * hstat
  apply (div_le_iff₀ (denominator_positive r hr)).2
  have hquartic : 0 ≤
      (T - 1) * r ^ 4 + (4 * T + 2 * α * (T - 1)) * r ^ 3 +
      (8 * T - 30 + 8 * α * T + 3 * α ^ 2 * (T - 1)) * r ^ 2 +
      (16 * T + 16 * α * T - 60 * α + 12 * α ^ 2 * T + 4 * α ^ 3 * (T - 1)) * r +
      (20 * T - 90 + 32 * α * T + (24 * T - 90) * α ^ 2 +
        16 * T * α ^ 3 + 5 * (T - 1) * α ^ 4) := by positivity
  nlinarith only [hidentity, mul_nonneg (sq_nonneg (r - α)) hquartic]

private def equalMoment (a b c : ℝ) : ℝ :=
  (a ^ 2 + b ^ 2 + c ^ 2) ^ 3 +
    6 * (a ^ 2 + b ^ 2 + c ^ 2) * ((b * (a + c)) ^ 2 + (a * c) ^ 2) +
    6 * (b * (a + c)) ^ 2 * (a * c)

private theorem equal_spacing_bound (T : ℝ) (hT : 5 / 4 < T)
    (hsym : ∀ r : ℝ, 0 ≤ r → thresholdN r / thresholdD r ≤ T)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hone : a + b + c = 1) :
    equalMoment a b c ≤ T * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  let s := a + c
  let A := s ^ 2 + b ^ 2
  let B := b ^ 2 * s ^ 2
  let ell := b ^ 2 + s ^ 2 / 2
  let u := a ^ 2 + b ^ 2 + c ^ 2
  let F := fun v : ℝ => (5 / 2) * v - 3 * A +
    (3 / 2) * (A ^ 2 + 2 * B) / v + 3 * A * B / v ^ 2
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsum : s + b = 1 := by dsimp [s]; linarith
  have hA : 0 < A := by dsimp [A]; nlinarith [sq_nonneg (s - b)]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hell : 0 < ell := by dsimp [ell]; nlinarith [sq_nonneg (s - b)]
  have hlu : ell ≤ u := by dsimp [ell, u, s]; nlinarith [sq_nonneg (a - c)]
  have huA : u ≤ A := by dsimp [u, A, s]; nlinarith [mul_nonneg ha hc]
  have hu : 0 < u := lt_of_lt_of_le hell hlu
  have hconv : ConvexOn ℝ (Set.Ioi 0) F := by
    have hid : ConvexOn ℝ (Set.Ioi 0) (fun v : ℝ => (5 / 2) * v) :=
      (convexOn_id (convex_Ioi (0 : ℝ))).smul (by norm_num)
    have hinv := (convexOn_zpow (-1 : ℤ) (𝕜 := ℝ)).smul
      (show 0 ≤ (3 / 2 : ℝ) * (A ^ 2 + 2 * B) by positivity)
    have hinvsq := (convexOn_zpow (-2 : ℤ) (𝕜 := ℝ)).smul
      (show 0 ≤ 3 * A * B by positivity)
    have hcv := ((hid.add_const (-3 * A)).add hinv).add hinvsq
    change ConvexOn ℝ (Set.Ioi 0) (fun v : ℝ =>
      ((5 / 2) * v + -3 * A) + ((3 / 2) * (A ^ 2 + 2 * B)) * v ^ (-1 : ℤ) +
        (3 * A * B) * v ^ (-2 : ℤ)) at hcv
    simpa [F, zpow_neg, zpow_natCast, div_eq_mul_inv, sub_eq_add_neg] using hcv
  have hleft : F ell ≤ T := by
    by_cases hszero : s = 0
    · have hb_one : b = 1 := by linarith
      dsimp [F, ell, A, B]
      rw [hszero, hb_one]
      norm_num
      linarith
    · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hszero)
      have hr : 0 ≤ 2 * b / s := by positivity
      have heq : F ell = thresholdN (2 * b / s) / thresholdD (2 * b / s) := by
        dsimp [F, ell, A, B, thresholdN, thresholdD]
        rw [show b = 1 - s by linarith]
        field_simp
        ring
      rw [heq]
      exact hsym _ hr
  have hright : F A ≤ T := by
    have htwo : A + 6 * (b * s) ^ 2 / A ≤ (5 / 4 : ℝ) := by
      have hw : 0 ≤ b * s := mul_nonneg hb hs
      have hwupper : b * s ≤ 1 / 4 := by nlinarith [sq_nonneg (b - s)]
      have hAeq : A = 1 - 2 * (b * s) := by dsimp [A]; nlinarith [hsum]
      have hfactor : 0 ≤ (1 - 4 * (b * s)) * (1 + 10 * (b * s)) :=
        mul_nonneg (by linarith) (by positivity)
      have hineq : A ^ 2 + 6 * (b * s) ^ 2 ≤ (5 / 4 : ℝ) * A := by
        rw [hAeq]
        nlinarith only [hfactor]
      have heq : A + 6 * (b * s) ^ 2 / A = (A ^ 2 + 6 * (b * s) ^ 2) / A := by
        field_simp
      rw [heq]
      exact (div_le_iff₀ hA).2 hineq
    have heq : F A = A + 6 * (b * s) ^ 2 / A := by
      dsimp [F, B]
      field_simp
      ring
    rw [heq]
    exact htwo.trans hT.le
  have hmax := (hconv.le_max_of_mem_Icc hell hA ⟨hlu, huA⟩).trans (max_le hleft hright)
  have heq : F u = equalMoment a b c / u ^ 2 := by
    dsimp [F, A, B, equalMoment]
    field_simp
    dsimp [u, s]
    ring
  rw [heq] at hmax
  exact (div_le_iff₀ (sq_pos_of_pos hu)).mp hmax

private theorem signal_bound (T : ℝ) (hT : 5 / 4 < T)
    (hsym : ∀ r : ℝ, 0 ≤ r → thresholdN r / thresholdD r ≤ T)
    {d L : ℕ} (n : Fin d → ℤ) (χ : Fin d → ℂ) (ψ : Fin L → Fin d → ℂ)
    (w : Fin L → ℝ) (hχ : IsUnitVector χ)
    (hψ : ∀ l, IsUnitVector (ψ l) ∧ IsThreeSparse (ψ l))
    (hw : ∀ l, 0 ≤ w l) (hwone : ∑ l, w l = 1)
    (hm : 0 < moment 1 (mixedSignal n χ ψ w)) :
    ratio3 (mixedSignal n χ ψ w) ≤ T := by
  sorry

private theorem threshold_attained (α : ℝ) (hα : 0 ≤ α) :
    thresholdN α / thresholdD α ∈ admissibleValues := by
  sorry

/-- The sharp three-coherence threshold, including arbitrary integer spectra and mixtures. -/
theorem result : claim := by
  obtain ⟨α, hl, hh, hp⟩ := root_exists
  obtain ⟨hT, hsym⟩ := threshold_bound α hl hh hp
  refine ⟨α, hl, hh, hp, threshold_attained α (by linarith), ?_⟩
  rintro v ⟨d, L, n, χ, ψ, w, hχ, hψ, hw, hwone, hm, rfl⟩
  exact signal_bound _ hT hsym n χ ψ w hχ hψ hw hwone hm

end D5.S3.Quantum.Measurement.ThreeCoherenceRamseyThreshold
