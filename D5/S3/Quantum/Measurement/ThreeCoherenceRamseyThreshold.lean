/- GID: D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The exact three-coherence Ramsey third-moment threshold. -/

import D5.S3.Quantum.Measurements.IQP.LidarRestrictedAnticoncentrationRefutation

/-! # The sharp three-coherence Ramsey threshold -/

noncomputable section

open Complex Real MeasureTheory Finset
open scoped BigOperators
open D5.S3.Quantum.Measurements.IQP.LidarRestrictedAnticoncentrationRefutation
open OpLidarTwinProbability (normSq_finite_sum)

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
  simp only [character.eq_1, Complex.star_def, ← Complex.exp_conj, map_mul, map_intCast,
    Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add, Int.cast_sub]
  congr 1
  ring

private theorem character_average (k : ℤ) :
    average (character k) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [average, character, Complex.ofReal_mul, Complex.ofReal_ofNat]
    simpa only [div_eq_mul_inv, mul_inv, mul_comm] using
      div_self (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
        (by norm_num : (2 : ℂ) ≠ 0))
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
  simp only [average.eq_1, intervalIntegral.integral_finsetSum
    (fun i _ => (hf i).intervalIntegrable _ _), Finset.mul_sum]

private theorem moment_one_formula {ι : Type*} [Fintype ι]
    (n : ι → ℤ) (z : ι → ℂ) :
    moment 1 (fun t => Complex.normSq (trigPoly n z t)) =
      ∑ i, ∑ j, if n i = n j then (z i * star (z j)).re else 0 := by
  classical
  have hpoint (t : ℝ) : (Complex.normSq (trigPoly n z t) : ℂ) =
      ∑ i, ∑ j, (z i * star (z j)) * character (n i - n j) t := by
    rw [trigPoly, normSq_finite_sum (fun j => z j * character (n j) t)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [star_mul, ← character_mul_star]
    ring
  have hcast : (moment 1 (fun t => Complex.normSq (trigPoly n z t)) : ℂ) =
      ∑ i, ∑ j, if n i = n j then z i * star (z j) else 0 := by
    simp only [moment.eq_1, pow_one, Complex.ofReal_mul, Complex.ofReal_div,
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
  have hlow : 0 < thresholdP (6169 / 5000) := by norm_num [thresholdP.eq_1]
  have hhigh : thresholdP (12339 / 10000) < 0 := by norm_num [thresholdP.eq_1]
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
      thresholdN (6169 / 5000) := by norm_num [thresholdN.eq_1, thresholdD.eq_1]
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
  have hquartic : 0 <
      (T - 1) * r ^ 4 + (4 * T + 2 * α * (T - 1)) * r ^ 3 +
      (8 * T - 30 + 8 * α * T + 3 * α ^ 2 * (T - 1)) * r ^ 2 +
      (16 * T + 16 * α * T - 60 * α + 12 * α ^ 2 * T + 4 * α ^ 3 * (T - 1)) * r +
      (20 * T - 90 + 32 * α * T + (24 * T - 90) * α ^ 2 +
        16 * T * α ^ 3 + 5 * (T - 1) * α ^ 4) := by positivity
  nlinarith only [hidentity, mul_nonneg (sq_nonneg (r - α)) hquartic.le]

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
        field_simp (disch := positivity)
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
        field_simp (disch := positivity)
      rw [heq]
      exact (div_le_iff₀ hA).2 hineq
    have heq : F A = A + 6 * (b * s) ^ 2 / A := by
      dsimp [F, B]
      field_simp (disch := positivity)
      ring
    rw [heq]
    exact htwo.trans hT.le
  have hmax := (hconv.le_max_of_mem_Icc hell hA ⟨hlu, huA⟩).trans (max_le hleft hright)
  have heq : F u = equalMoment a b c / u ^ 2 := by
    dsimp [F, A, B, equalMoment]
    field_simp (disch := positivity)
    dsimp [u, s]
    ring
  rw [heq] at hmax
  exact (div_le_iff₀ (sq_pos_of_pos hu)).mp hmax

private def cubicEnergy (n : Fin 3 → ℤ) : Fin 10 → ℤ :=
  ![3 * n 0, 2 * n 0 + n 1, 2 * n 0 + n 2, n 0 + 2 * n 1,
    n 0 + n 1 + n 2, n 0 + 2 * n 2, 3 * n 1, 2 * n 1 + n 2,
    n 1 + 2 * n 2, 3 * n 2]

private def cubicCoefficient {R : Type*} [CommSemiring R] (a b c : R) : Fin 10 → R :=
  ![a ^ 3, 3 * a ^ 2 * b, 3 * a ^ 2 * c, 3 * a * b ^ 2, 6 * a * b * c,
    3 * a * c ^ 2, b ^ 3, 3 * b ^ 2 * c, 3 * b * c ^ 2, c ^ 3]

private theorem character_add (k m : ℤ) (t : ℝ) :
    character (k + m) t = character k t * character m t := by
  simp [character, Int.cast_add, add_mul, Complex.exp_add]

private theorem character_nat_mul (q : ℕ) (k : ℤ) (t : ℝ) :
    character ((q : ℤ) * k) t = character k t ^ q := by
  simp only [character, Int.cast_mul, Int.cast_natCast]
  rw [show (q : ℂ) * (k : ℂ) * t * I = q * ((k : ℂ) * t * I) by ring,
    Complex.exp_nat_mul]

private theorem cubic_expansion (n : Fin 3 → ℤ) (a b c : ℂ) (t : ℝ) :
    trigPoly n ![a, b, c] t ^ 3 = trigPoly (cubicEnergy n) (cubicCoefficient a b c) t := by
  simp only [trigPoly, cubicEnergy, cubicCoefficient, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  have htwo (k : ℤ) : character (2 * k) t = character k t ^ 2 := character_nat_mul 2 k t
  have hthree (k : ℤ) : character (3 * k) t = character k t ^ 3 := character_nat_mul 3 k t
  simp only [character_add, htwo, hthree]
  ring

private theorem cubic_collision (n : Fin 3 → ℤ) (h01 : n 0 < n 1) (h12 : n 1 < n 2)
    (i j : Fin 10) : cubicEnergy n i = cubicEnergy n j ↔
      i = j ∨
      (n 0 + n 2 = 2 * n 1 ∧
        ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨ (i = 4 ∧ j = 6) ∨
         (i = 6 ∧ j = 4) ∨ (i = 5 ∧ j = 7) ∨ (i = 7 ∧ j = 5))) ∨
      (2 * n 0 + n 2 = 3 * n 1 ∧ ((i = 2 ∧ j = 6) ∨ (i = 6 ∧ j = 2))) ∨
      (n 0 + 2 * n 2 = 3 * n 1 ∧ ((i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5))) := by
  fin_cases i <;> fin_cases j <;> norm_num [cubicEnergy.eq_1] <;> omega

private theorem cubic_moment_formula (n : Fin 3 → ℤ) (a b c : ℝ) :
    moment 3 (fun t => Complex.normSq (trigPoly n ![(a : ℂ), b, c] t)) =
      ∑ i : Fin 10, ∑ j : Fin 10, if cubicEnergy n i = cubicEnergy n j then
        cubicCoefficient a b c i * cubicCoefficient a b c j else 0 := by
  have hcoeff (i : Fin 10) : cubicCoefficient (a : ℂ) b c i =
      ((cubicCoefficient (R := ℝ) a b c i : ℝ) : ℂ) := by
    fin_cases i <;> simp [cubicCoefficient.eq_1]
  calc
    _ = moment 1 (fun t => Complex.normSq
        (trigPoly (cubicEnergy n) (cubicCoefficient (a : ℂ) b c) t)) := by
      simp only [moment, pow_one, ← map_pow, cubic_expansion]
    _ = _ := by
      rw [moment_one_formula]
      simp only [hcoeff, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Complex.ofReal_re]

private theorem spacing_bound (n : Fin 3 → ℤ) (h01 : n 0 < n 1) (h12 : n 1 < n 2)
    (a b c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    moment 3 (fun t => Complex.normSq (trigPoly n ![(a : ℂ), b, c] t)) ≤
      equalMoment a b c := by
  rw [cubic_moment_formula]
  simp_rw [cubic_collision n h01 h12]
  by_cases h0 : n 0 + n 2 = 2 * n 1
  · have h1 : ¬2 * n 0 + n 2 = 3 * n 1 := by omega
    have h2 : ¬n 0 + 2 * n 2 = 3 * n 1 := by omega
    simp [h0, h1, h2, Fin.sum_univ_succ, cubicCoefficient, equalMoment]
    ring_nf
    exact le_rfl
  · by_cases h1 : 2 * n 0 + n 2 = 3 * n 1
    · have h2 : ¬n 0 + 2 * n 2 = 3 * n 1 := by omega
      simp [h0, h1, h2, Fin.sum_univ_succ, cubicCoefficient, equalMoment]
      nlinarith [mul_nonneg (by positivity : 0 ≤ 6 * a * b ^ 2 * c)
        (by nlinarith [sq_nonneg (a - b)] : 0 ≤ 3 * a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2 - a * b)]
    · by_cases h2 : n 0 + 2 * n 2 = 3 * n 1
      · simp [h0, h1, h2, Fin.sum_univ_succ, cubicCoefficient, equalMoment]
        nlinarith [mul_nonneg (by positivity : 0 ≤ 6 * a * b ^ 2 * c)
          (by nlinarith [sq_nonneg (b - c)] : 0 ≤ 3 * a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2 - b * c)]
      · simp [h0, h1, h2, Fin.sum_univ_succ, cubicCoefficient, equalMoment]
        nlinarith [mul_nonneg (by positivity : 0 ≤ 6 * a * b ^ 2 * c)
          (by positivity : 0 ≤ 3 * a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2)]

private theorem subunit_equal_bound (T : ℝ) (hT : 5 / 4 < T)
    (hsym : ∀ r : ℝ, 0 ≤ r → thresholdN r / thresholdD r ≤ T)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hone : a + b + c ≤ 1) :
    equalMoment a b c ≤ T * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  let s := a + b + c
  by_cases hzero : s = 0
  · have hazero : a = 0 := by dsimp [s] at hzero; linarith
    have hbzero : b = 0 := by dsimp [s] at hzero; linarith
    have hczero : c = 0 := by dsimp [s] at hzero; linarith
    simp [hazero, hbzero, hczero, equalMoment.eq_1]
  · have hs : 0 < s := lt_of_le_of_ne (by dsimp [s]; positivity) (Ne.symm hzero)
    have hnorm : a / s + b / s + c / s = 1 := by
      rw [← add_div, ← add_div]
      exact div_self hzero
    have hscaled := equal_spacing_bound T hT hsym (a / s) (b / s) (c / s)
      (by positivity) (by positivity) (by positivity) hnorm
    have heq : equalMoment a b c = s ^ 6 * equalMoment (a / s) (b / s) (c / s) := by
      dsimp [equalMoment]
      field_simp (disch := positivity)
    have hu : (a / s) ^ 2 + (b / s) ^ 2 + (c / s) ^ 2 =
        (a ^ 2 + b ^ 2 + c ^ 2) / s ^ 2 := by field_simp (disch := positivity)
    rw [hu] at hscaled
    have hmul := mul_le_mul_of_nonneg_left hscaled (pow_nonneg hs.le 6)
    rw [← heq] at hmul
    have hcancel : s ^ 6 * (T * ((a ^ 2 + b ^ 2 + c ^ 2) / s ^ 2) ^ 2) =
        T * s ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by field_simp (disch := positivity)
    rw [hcancel] at hmul
    have hsone : s ^ 2 ≤ 1 := by dsimp [s]; nlinarith
    have hTzero : 0 ≤ T := by linarith
    have hmul2 := mul_le_mul_of_nonneg_right hsone
      (mul_nonneg hTzero (sq_nonneg (a ^ 2 + b ^ 2 + c ^ 2)))
    nlinarith only [hmul, hmul2]

private theorem coefficient_bound (T : ℝ) (hT : 5 / 4 < T)
    (hsym : ∀ r : ℝ, 0 ≤ r → thresholdN r / thresholdD r ≤ T)
    (n : Fin 3 → ℤ) (hn : StrictMono n) (z : Fin 3 → ℂ) (hz : ∑ i, ‖z i‖ ≤ 1) :
    moment 3 (fun t => Complex.normSq (trigPoly n z t)) ≤
      T * moment 1 (fun t => Complex.normSq (trigPoly n z t)) ^ 2 := by
  have hvec : (fun i => (‖z i‖ : ℂ)) = ![(‖z 0‖ : ℂ), ‖z 1‖, ‖z 2‖] := by
    funext i
    fin_cases i <;> rfl
  have hnorm : ‖z 0‖ + ‖z 1‖ + ‖z 2‖ ≤ 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hz
  calc
    _ ≤ moment 3 (fun t => Complex.normSq (trigPoly n (fun i => (‖z i‖ : ℂ)) t)) :=
      moment_abs_le n z 3
    _ ≤ equalMoment ‖z 0‖ ‖z 1‖ ‖z 2‖ := by
      rw [hvec]
      exact spacing_bound n (hn (by decide)) (hn (by decide)) _ _ _
        (norm_nonneg _) (norm_nonneg _)
    _ ≤ T * (‖z 0‖ ^ 2 + ‖z 1‖ ^ 2 + ‖z 2‖ ^ 2) ^ 2 :=
      subunit_equal_bound T hT hsym _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hnorm
    _ = _ := by rw [moment_one_injective n z hn.injective]; simp [Fin.sum_univ_succ, add_assoc]

private theorem pure_representation {d : ℕ} (n : Fin d → ℤ) (χ ψ : Fin d → ℂ)
    (hχ : IsUnitVector χ) (hψ : IsUnitVector ψ) (hsparse : IsThreeSparse ψ) :
    ∃ (e : Fin 3 → ℤ) (z : Fin 3 → ℂ), StrictMono e ∧ (∑ i, ‖z i‖ ≤ 1) ∧
      ∀ t, signal n χ ψ t = Complex.normSq (trigPoly e z t) := by
  classical
  let S := (Function.support ψ).toFinite.toFinset
  have hS : S.card ≤ 3 := by
    rw [← Set.ncard_eq_toFinset_card]
    exact hsparse
  let energy := fun j : Fin d => -n j
  obtain ⟨F, hsubset, hcard⟩ := Infinite.exists_superset_card_eq (S.image energy) 3
    ((Finset.card_image_le).trans hS)
  let e := F.orderEmbOfFin hcard
  let Z := fun h : ℤ => ∑ j ∈ S with energy j = h, star (χ j) * ψ j
  have hmap : ∀ j ∈ S, energy j ∈ F := fun j hj =>
    hsubset (Finset.mem_image_of_mem energy hj)
  have hsum (f : ℤ → ℝ) : ∑ i, f (e i) = ∑ h ∈ F, f h := by
    rw [← Finset.image_orderEmbOfFin_univ F hcard, Finset.sum_image]
    exact fun i _ j _ hij => e.injective hij
  have hsumC (f : ℤ → ℂ) : ∑ i, f (e i) = ∑ h ∈ F, f h := by
    rw [← Finset.image_orderEmbOfFin_univ F hcard, Finset.sum_image]
    exact fun i _ j _ hij => e.injective hij
  refine ⟨e, fun i => Z (e i), e.strictMono, ?_, ?_⟩
  · rw [hsum (fun h => ‖Z h‖)]
    calc
      _ ≤ ∑ h ∈ F, ∑ j ∈ S with energy j = h, ‖star (χ j) * ψ j‖ := by
        apply Finset.sum_le_sum
        intro h _
        exact norm_sum_le _ _
      _ = ∑ j ∈ S, ‖star (χ j) * ψ j‖ := Finset.sum_fiberwise_of_maps_to hmap _
      _ ≤ ∑ j, ‖χ j‖ * ‖ψ j‖ := by
        simp only [norm_mul, norm_star]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => by positivity)
      _ ≤ 1 := by
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖χ j‖) (fun j => ‖ψ j‖)
        simp only [← Complex.normSq_eq_norm_sq] at hcs
        rw [hχ, hψ] at hcs
        have hnonneg : 0 ≤ ∑ j, ‖χ j‖ * ‖ψ j‖ := by positivity
        nlinarith
  · intro t
    unfold signal
    congr 1
    rw [trigPoly, hsumC (fun h => Z h * character h t)]
    simp only [Z, Finset.sum_mul]
    have hfiber : (∑ h ∈ F, ∑ j ∈ S with energy j = h,
        (star (χ j) * ψ j) * character h t) =
        ∑ j ∈ S, (star (χ j) * ψ j) * character (energy j) t := by
      calc
        _ = ∑ h ∈ F, ∑ j ∈ S with energy j = h,
            (star (χ j) * ψ j) * character (energy j) t := by
          apply Finset.sum_congr rfl
          intro h _
          apply Finset.sum_congr rfl
          intro j hj
          rw [(Finset.mem_filter.mp hj).2]
        _ = _ := Finset.sum_fiberwise_of_maps_to hmap _
    rw [hfiber]
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · apply Finset.sum_congr rfl
      intro j _
      simp only [character, energy, Int.cast_neg]
      ring
    · intro j _ hj
      have hzero : ψ j = 0 := by
        simpa only [S, Set.Finite.mem_toFinset, Function.mem_support, not_not] using hj
      simp [hzero]

private theorem pure_bound (T : ℝ) (hT : 5 / 4 < T)
    (hsym : ∀ r : ℝ, 0 ≤ r → thresholdN r / thresholdD r ≤ T)
    {d : ℕ} (n : Fin d → ℤ) (χ ψ : Fin d → ℂ)
    (hχ : IsUnitVector χ) (hψ : IsUnitVector ψ) (hsparse : IsThreeSparse ψ) :
    moment 3 (signal n χ ψ) ≤ T * moment 1 (signal n χ ψ) ^ 2 := by
  obtain ⟨e, z, he, hz, hsignal⟩ := pure_representation n χ ψ hχ hψ hsparse
  simp_rw [show signal n χ ψ = (fun t => Complex.normSq (trigPoly e z t)) from funext hsignal]
  exact coefficient_bound T hT hsym e he z hz

private theorem weighted_cube {ι : Type*} [Fintype ι] (w p b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, 0 ≤ p i) (hb : ∀ i, 0 < b i)
    (s : ℝ) (hs : 0 < s) (hone : ∑ i, w i * b i = s) :
    (∑ i, w i * p i) ^ 3 ≤ s ^ 2 * ∑ i, w i * (p i ^ 3 / b i ^ 2) := by
  have huone : ∑ i, w i * b i / s = 1 := by rw [← Finset.sum_div, hone, div_self hs.ne']
  have hj := Real.pow_arith_mean_le_arith_mean_pow Finset.univ
    (fun i => w i * b i / s) (fun i => p i / b i)
    (fun i _ => div_nonneg (mul_nonneg (hw i) (hb i).le) hs.le) huone
    (fun i _ => div_nonneg (hp i) (hb i).le) 3
  have hlinear : ∑ i, (w i * b i / s) * (p i / b i) = (∑ i, w i * p i) / s := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp (disch := first | exact (hb i).ne' | positivity)
  have hcubic : ∑ i, (w i * b i / s) * (p i / b i) ^ 3 =
      (∑ i, w i * (p i ^ 3 / b i ^ 2)) / s := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp (disch := first | exact (hb i).ne' | positivity)
  rw [hlinear, hcubic, div_pow] at hj
  apply (mul_le_mul_iff_right₀ hs).mp
  rw [mul_comm s]
  calc
    _ ≤ (∑ i, w i * (p i ^ 3 / b i ^ 2)) * s ^ 3 :=
      (div_le_div_iff₀ (pow_pos hs 3) hs).mp hj
    _ = _ := by ring

private theorem moment_one_mixture {L : ℕ} (p : Fin L → ℝ → ℝ) (w : Fin L → ℝ)
    (hp : ∀ l, Continuous (p l)) :
    moment 1 (fun t => ∑ l, w l * p l t) = ∑ l, w l * moment 1 (p l) := by
  simp only [moment, pow_one]
  rw [intervalIntegral.integral_finsetSum (f := fun l t => w l * p l t)
    (fun l _ => (continuous_const.mul (hp l)).intervalIntegrable _ _), Finset.mul_sum]
  simp only [intervalIntegral.integral_const_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

private theorem mixture_bound {L : ℕ} (p : Fin L → ℝ → ℝ) (w : Fin L → ℝ)
    (hp : ∀ l, Continuous (p l)) (hnonneg : ∀ l t, 0 ≤ p l t)
    (hw : ∀ l, 0 ≤ w l) (hwone : ∑ l, w l = 1)
    (T : ℝ) (hT : 0 ≤ T) (hbound : ∀ l, moment 3 (p l) ≤ T * moment 1 (p l) ^ 2) :
    moment 3 (fun t => ∑ l, w l * p l t) ≤
      T * moment 1 (fun t => ∑ l, w l * p l t) ^ 2 := by
  let m := moment 1 (fun t => ∑ l, w l * p l t)
  have hml : ∀ l, 0 ≤ moment 1 (p l) := by
    intro l
    exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg_of_forall
      (by positivity) (fun t => by simpa using hnonneg l t))
  have hmeq : m = ∑ l, w l * moment 1 (p l) := moment_one_mixture p w hp
  have hm : 0 ≤ m := by rw [hmeq]; exact Finset.sum_nonneg (fun l _ => mul_nonneg (hw l) (hml l))
  have heps (ε : ℝ) (hε : 0 < ε) :
      moment 3 (fun t => ∑ l, w l * p l t) ≤ T * (m + ε) ^ 2 := by
    have hs : 0 < m + ε := by positivity
    have hsum : ∑ l, w l * (moment 1 (p l) + ε) = m + ε := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [hwone, hmeq]
      ring
    have hpoint (t : ℝ) : (∑ l, w l * p l t) ^ 3 ≤
        (m + ε) ^ 2 * ∑ l, w l * (p l t ^ 3 / (moment 1 (p l) + ε) ^ 2) :=
      weighted_cube w (fun l => p l t) (fun l => moment 1 (p l) + ε)
        hw (fun l => hnonneg l t) (fun l => by linarith [hml l]) _ hs hsum
    have hint : moment 3 (fun t => ∑ l, w l * p l t) ≤
        (m + ε) ^ 2 * ∑ l, w l * (moment 3 (p l) / (moment 1 (p l) + ε) ^ 2) := by
      calc
        _ ≤ (1 / (2 * π)) * ∫ t in (0)..(2 * π),
            (m + ε) ^ 2 * ∑ l, w l * (p l t ^ 3 / (moment 1 (p l) + ε) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact intervalIntegral.integral_mono_on (by positivity)
            (by apply Continuous.intervalIntegrable; fun_prop)
            (by apply Continuous.intervalIntegrable; fun_prop) (fun t _ => hpoint t)
        _ = _ := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
            (fun l _ => (by fun_prop : Continuous
              (fun t => w l * (p l t ^ 3 / (moment 1 (p l) + ε) ^ 2))).intervalIntegrable _ _)]
          simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_div, moment]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
    have hterm (l : Fin L) : moment 3 (p l) / (moment 1 (p l) + ε) ^ 2 ≤ T := by
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith [hml l]))).2
      exact (hbound l).trans (mul_le_mul_of_nonneg_left (by nlinarith [hml l]) hT)
    have hsum_bound : (∑ l, w l * (moment 3 (p l) / (moment 1 (p l) + ε) ^ 2)) ≤ T := by
      calc
        _ ≤ ∑ l, w l * T := Finset.sum_le_sum
          (fun l _ => mul_le_mul_of_nonneg_left (hterm l) (hw l))
        _ = T := by rw [← Finset.sum_mul, hwone, one_mul]
    exact hint.trans (by nlinarith [mul_le_mul_of_nonneg_left hsum_bound (sq_nonneg (m + ε))])
  have hcont : ContinuousAt (fun ε : ℝ => T * (m + ε) ^ 2) 0 := by fun_prop
  have hlimit := ge_of_tendsto hcont.continuousWithinAt.tendsto
    (show ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      moment 3 (fun t => ∑ l, w l * p l t) ≤ T * (m + ε) ^ 2 from
      Filter.mem_of_superset self_mem_nhdsWithin (fun ε hε => heps ε hε))
  simpa using hlimit

private theorem signal_continuous {d : ℕ} (n : Fin d → ℤ) (χ ψ : Fin d → ℂ) :
    Continuous (signal n χ ψ) := by
  unfold signal
  fun_prop

private theorem signal_bound (T : ℝ) (hT : 5 / 4 < T)
    (hsym : ∀ r : ℝ, 0 ≤ r → thresholdN r / thresholdD r ≤ T)
    {d L : ℕ} (n : Fin d → ℤ) (χ : Fin d → ℂ) (ψ : Fin L → Fin d → ℂ)
    (w : Fin L → ℝ) (hχ : IsUnitVector χ)
    (hψ : ∀ l, IsUnitVector (ψ l) ∧ IsThreeSparse (ψ l))
    (hw : ∀ l, 0 ≤ w l) (hwone : ∑ l, w l = 1)
    (hm : 0 < moment 1 (mixedSignal n χ ψ w)) :
    ratio3 (mixedSignal n χ ψ w) ≤ T := by
  have hmix := mixture_bound (fun l => signal n χ (ψ l)) w
    (fun l => signal_continuous n χ (ψ l)) (fun l t => Complex.normSq_nonneg _)
    hw hwone T (by linarith)
    (fun l => pure_bound T hT hsym n χ (ψ l) hχ (hψ l).1 (hψ l).2)
  exact (div_le_iff₀ (sq_pos_of_pos hm)).2 hmix

private theorem threshold_attained (α : ℝ) (hα : 0 ≤ α) :
    thresholdN α / thresholdD α ∈ admissibleValues := by
  let a := 1 / (α + 2)
  let b := α / (α + 2)
  have hden : 0 < α + 2 := by positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hone : a + b + a = 1 := by dsimp [a, b]; field_simp (disch := positivity); ring
  let v : Fin 3 → ℂ := ![(Real.sqrt a : ℂ), Real.sqrt b, Real.sqrt a]
  have hv : IsUnitVector v := by
    simpa [IsUnitVector.eq_1, v, Fin.sum_univ_succ, Real.mul_self_sqrt ha.le,
      Real.mul_self_sqrt hb, add_assoc] using hone
  have hsparse : IsThreeSparse v :=
    (Set.ncard_le_card _).trans (by simp)
  let e : Fin 3 → ℤ := ![0, -1, -2]
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [e] at *
  have hsquare (x : ℝ) (hx : 0 ≤ x) (E : ℂ) :
      star (Real.sqrt x : ℂ) * E * (Real.sqrt x : ℂ) = (x : ℂ) * E := by
    rw [Complex.star_def, Complex.conj_ofReal]
    calc
      _ = ((Real.sqrt x : ℂ) * (Real.sqrt x : ℂ)) * E := by ring
      _ = _ := by rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx]
  have hsignal : signal (![0, 1, 2] : Fin 3 → ℤ) v v =
      (fun t => Complex.normSq (trigPoly e ![(a : ℂ), b, a] t)) := by
    funext t
    unfold signal trigPoly
    congr 1
    simp only [v, e, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.isValue, hsquare a ha.le, hsquare b hb]
    norm_num [character]
  have hmone : moment 1 (signal (![0, 1, 2] : Fin 3 → ℤ) v v) = 2 * a ^ 2 + b ^ 2 := by
    rw [hsignal, moment_one_injective e _ he]
    simp [Fin.sum_univ_succ, Complex.norm_real, Real.norm_eq_abs]
    ring
  have hmthree : moment 3 (signal (![0, 1, 2] : Fin 3 → ℤ) v v) = equalMoment a b a := by
    rw [hsignal, cubic_moment_formula]
    norm_num [e, Fin.sum_univ_succ, cubicEnergy, cubicCoefficient, equalMoment]
    ring
  have hratio : ratio3 (signal (![0, 1, 2] : Fin 3 → ℤ) v v) = thresholdN α / thresholdD α := by
    rw [ratio3, hmone, hmthree]
    dsimp [equalMoment, a, b, thresholdN, thresholdD]
    field_simp (disch := positivity)
    ring
  have hmix : mixedSignal (![0, 1, 2] : Fin 3 → ℤ) v (fun _ : Fin 1 => v) (fun _ => 1) =
      signal (![0, 1, 2] : Fin 3 → ℤ) v v := by
    funext t
    simp [mixedSignal.eq_1]
  refine ⟨3, 1, ![0, 1, 2], v, (fun _ => v), (fun _ => 1), hv,
    (fun _ => ⟨hv, hsparse⟩), (fun _ => by norm_num), by simp, ?_, ?_⟩
  · rw [hmix, hmone]
    positivity
  · rw [hmix]
    exact hratio.symm

/-- The sharp three-coherence threshold, including arbitrary integer spectra and mixtures. -/
theorem result : claim := by
  obtain ⟨α, hl, hh, hp⟩ := root_exists
  obtain ⟨hT, hsym⟩ := threshold_bound α hl hh hp
  refine ⟨α, hl, hh, hp, threshold_attained α (by linarith), ?_⟩
  rintro v ⟨d, L, n, χ, ψ, w, hχ, hψ, hw, hwone, hm, rfl⟩
  exact signal_bound _ hT hsym n χ ψ w hχ hψ hw hwone hm

end D5.S3.Quantum.Measurement.ThreeCoherenceRamseyThreshold
