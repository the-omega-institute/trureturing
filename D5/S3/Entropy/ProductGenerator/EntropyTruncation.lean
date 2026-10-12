/- GID: D5/S3/Entropy/ProductGenerator/EntropyTruncation
   generality: G
   mirror-B: D5/B/S3/Entropy/ProductGenerator/EntropyTruncation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entropy truncation for exact finite product sources of an interior parity law. -/

import D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
import D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Entropy.ProductGenerator.EntropyTruncation
noncomputable section

open D5.S3.Entropy.MaxEntropy
open D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments (paritySign)

local notation "σ" => (fun b : Fin 2 => ((paritySign b : ℤ) : ℝ))

open D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy (windowLaw windowLaw_sum_eq_one)
local notation "productChannel" =>
  (fun {n : ℕ} (m : Fin n → ℝ) =>
    windowLaw (fun (i : Fin n) (b : Fin 2) => (1 + m i * σ b) / 2))

/-- The interior parity law, including its fair normalization. -/
def parityMass {n : ℕ} (κ : ℝ) (x : Fin n → Fin 2) : ℝ :=
  (2 : ℝ)⁻¹ ^ n * (1 + κ * ∏ i, σ (x i))

/-- All parameters of one exact finite product-source realization. -/
structure ExactGenerator (n : ℕ) (κ : ℝ) (Z : Type*) [Fintype Z] where
  weight : Z → ℝ
  mean : Z → Fin n → ℝ
  weight_pos : ∀ z, 0 < weight z
  weight_sum : ∑ z, weight z = 1
  mean_bound : ∀ z i, |mean z i| ≤ 1
  exact_mass : ∀ x, ∑ z, weight z * productChannel (mean z) x = parityMass κ x

local notation "componentMoment" => (fun {n : ℕ} (m : Fin n → ℝ) => ∏ i, m i)

/-- The total absolute parity charge in one realized generator. -/
def absoluteCharge {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) : ℝ :=
  ∑ z, G.weight z * |componentMoment (G.mean z)|

/-- The parity defect carried by labels below the entropy cutoff. -/
def smallDefect {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (L : ℝ) : ℝ :=
  ∑ z, if G.weight z < Real.exp (-L) then
    G.weight z * (1 - |componentMoment (G.mean z)|) else 0

/-- A logarithmic capacity bound and a cutoff force an affine charge bound,
with one error that also covers the zero-charge endpoint. -/
private theorem log_cutoff_chord {D L s t d c : ℝ}
    (hD : 0 ≤ D) (hL : 0 ≤ L) (_hLD : L ≤ D)
    (hs : 0 < s) (hs1 : s < 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hlog : 2 * (L - D) ≤ Real.log s)
    (hcut : L ≤ d + c)
    (hcap : 0 < t → D + Real.log t / 2 ≤ d + c) :
    D * t + L * (1 - t) - D * s / (1 - s) ≤ d + c := by
  have hden : 0 < 1 - s := by linarith
  by_cases hts : t ≤ s
  · have herr : D * s ≤ D * s / (1 - s) := by
      apply (le_div_iff₀ hden).2
      nlinarith [mul_nonneg hD (sq_nonneg s)]
    have hlinear : (D - L) * t ≤ D * s := by nlinarith
    linarith
  · have hst : s ≤ t := (lt_of_not_ge hts).le
    let a := (1 - t) / (1 - s)
    let b := (t - s) / (1 - s)
    have ha : 0 ≤ a := div_nonneg (by linarith) hden.le
    have hb : 0 ≤ b := div_nonneg (by linarith) hden.le
    have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
    have hblend : a * s + b * 1 = t := by dsimp [a, b]; field_simp; ring
    have hj := strictConcaveOn_log_Ioi.concaveOn.2 hs
      (show (0 : ℝ) < 1 by norm_num) ha hb hab
    simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero, hblend] at hj
    have hchord : L * a + D * b ≤ D + Real.log t / 2 := by
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hlog)]
    have hcompare : D * t + L * (1 - t) - D * s / (1 - s) ≤
        L * a + D * b := by
      apply (mul_le_mul_iff_left₀ hden).mp
      dsimp [a, b]
      field_simp
      nlinarith [mul_nonneg hs.le (add_nonneg (mul_nonneg hD ht)
        (mul_nonneg hL (sub_nonneg.mpr ht1)))]
    exact hcompare.trans (hchord.trans (hcap (hs.trans_le hst)))

private theorem productChannel_nonneg {n : ℕ} (m : Fin n → ℝ)
    (hm : ∀ i, |m i| ≤ 1) (x : Fin n → Fin 2) :
    0 ≤ productChannel m x := by
  apply Finset.prod_nonneg
  intro i _
  have hmi := abs_le.mp (hm i)
  generalize hx : x i = b
  fin_cases b <;> simp [paritySign] <;> linarith

private theorem componentMoment_abs_le_one {n : ℕ} (m : Fin n → ℝ)
    (hm : ∀ i, |m i| ≤ 1) : |componentMoment m| ≤ 1 := by
  rw [Finset.abs_prod]
  exact (Finset.prod_le_prod (fun i _ => abs_nonneg (m i))
    (fun i _ => hm i)).trans_eq (by simp)

private theorem weight_le_one {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (z : Z) : G.weight z ≤ 1 := by
  rw [← G.weight_sum]
  exact Finset.single_le_sum (fun z _ => (G.weight_pos z).le) (Finset.mem_univ z)

/-- A mode uses the sign of each mean, with positive sign at zero. -/
private def mode {n : ℕ} (m : Fin n → ℝ) : Fin n → Fin 2 :=
  fun i => if m i < 0 then 0 else 1

private theorem mode_mass {n : ℕ} (m : Fin n → ℝ) :
    productChannel m (mode m) = ∏ i, (1 + |m i|) / 2 := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : m i < 0
  · simp [mode, hi, paritySign, abs_of_neg hi]
  · simp [mode, hi, paritySign, abs_of_nonneg (le_of_not_gt hi)]

private theorem moment_le_mode_sq {n : ℕ} (m : Fin n → ℝ) :
    |componentMoment m| ≤ (productChannel m (mode m)) ^ 2 := by
  rw [Finset.abs_prod, mode_mass, ← Finset.prod_pow]
  apply Finset.prod_le_prod (fun i _ => abs_nonneg (m i))
  intro i _
  nlinarith [sq_nonneg (1 - |m i|)]

private theorem parityMass_le {n : ℕ} {κ : ℝ} (hκ : 0 ≤ κ)
    (x : Fin n → Fin 2) : parityMass κ x ≤ (2 : ℝ)⁻¹ ^ n * (1 + κ) := by
  have hpar : |∏ i, σ (x i)| ≤ 1 := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_one (fun i _ => abs_nonneg (σ (x i)))
    intro i _
    generalize hx : x i = b
    fin_cases b <;> norm_num [paritySign]
  dsimp [parityMass]
  have hupper := (abs_le.mp hpar).2
  have hp : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  exact mul_le_mul_of_nonneg_left (by nlinarith) hp

private theorem mode_capacity {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (hκ : 0 ≤ κ) (z : Z) :
    G.weight z * productChannel (G.mean z) (mode (G.mean z)) ≤
      (2 : ℝ)⁻¹ ^ n * (1 + κ) := by
  calc
    _ ≤ ∑ y, G.weight y * productChannel (G.mean y) (mode (G.mean z)) :=
      Finset.single_le_sum (fun y _ => mul_nonneg (G.weight_pos y).le
        (productChannel_nonneg (G.mean y) (G.mean_bound y) _)) (Finset.mem_univ z)
    _ = parityMass κ (mode (G.mean z)) := G.exact_mass _
    _ ≤ _ := parityMass_le hκ _

private theorem component_log_capacity {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (hκ : 0 ≤ κ) (z : Z)
    (ht : 0 < |componentMoment (G.mean z)|) :
    (n : ℝ) * Real.log 2 + Real.log |componentMoment (G.mean z)| / 2 ≤
      -Real.log (G.weight z) + Real.log (1 + κ) := by
  let q := productChannel (G.mean z) (mode (G.mean z))
  have hq0 : 0 ≤ q := productChannel_nonneg _ (G.mean_bound z) _
  have hq2 : |componentMoment (G.mean z)| ≤ q ^ 2 := moment_le_mode_sq _
  have hq : 0 < q := by nlinarith
  have hlog1 := Real.log_le_log ht hq2
  rw [Real.log_pow] at hlog1
  have hlog2 := Real.log_le_log (mul_pos (G.weight_pos z) hq) (mode_capacity G hκ z)
  rw [Real.log_mul (ne_of_gt (G.weight_pos z)) (ne_of_gt hq),
    Real.log_mul (pow_ne_zero n (by norm_num)) (by linarith : (1 + κ) ≠ 0),
    Real.log_pow, Real.log_inv] at hlog2
  norm_num only [Nat.cast_ofNat] at hlog1
  simp only [mul_neg] at hlog2
  linarith


private theorem channel_parity_moment {n : ℕ} (m : Fin n → ℝ) :
    (∑ x : Fin n → Fin 2, productChannel m x * ∏ i, σ (x i)) =
      componentMoment m := by
  simp only [windowLaw, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Fin 2) => (1 + m i * σ b) / 2 * σ b)]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  norm_num [paritySign]
  ring

private theorem law_parity_moment {n : ℕ} (hn : 0 < n) (κ : ℝ) :
    (∑ x : Fin n → Fin 2, parityMass κ x * ∏ i, σ (x i)) = κ := by
  have hzero : (∑ x : Fin n → Fin 2, ∏ i, σ (x i)) = 0 := by
    rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Fin 2) => σ b)]
    simp [Fin.sum_univ_two, paritySign, Nat.ne_of_gt hn]
  have hsquare (x : Fin n → Fin 2) : (∏ i, σ (x i)) ^ 2 = 1 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro i _
    generalize hx : x i = b
    fin_cases b <;> norm_num [paritySign]
  calc
    _ = (2 : ℝ)⁻¹ ^ n *
        ((∑ x : Fin n → Fin 2, ∏ i, σ (x i)) + κ *
          ∑ x : Fin n → Fin 2, (∏ i, σ (x i)) ^ 2) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      dsimp [parityMass]
      ring
    _ = κ := by
      simp only [hzero, hsquare, Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow,
        Nat.cast_ofNat, zero_add]
      have hp : (2 : ℝ)⁻¹ ^ n * 2 ^ n = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        _ = κ * ((2 : ℝ)⁻¹ ^ n * 2 ^ n) := by ring
        _ = κ := by rw [hp, mul_one]

private theorem generator_parity_moment {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (hn : 0 < n) :
    (∑ z, G.weight z * componentMoment (G.mean z)) = κ := by
  calc
    _ = ∑ z, G.weight z *
        ∑ x : Fin n → Fin 2, productChannel (G.mean z) x * ∏ i, σ (x i) := by
      simp_rw [channel_parity_moment]
    _ = ∑ x : Fin n → Fin 2, (∑ z, G.weight z * productChannel (G.mean z) x) *
        ∏ i, σ (x i) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    _ = κ := by simp_rw [G.exact_mass]; exact law_parity_moment hn κ

/-- Exact generation controls both excess absolute parity charge and the
small-label defect uniformly in the finite source alphabet. -/
theorem entropy_truncation_coercivity {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (hκ : 0 ≤ κ) (L g : ℝ)
    (hL : 0 ≤ L) (hLD : L < (n : ℝ) * Real.log 2)
    (hH : shannonEntropy G.weight ≤ (n : ℝ) * Real.log 2 * κ + g) :
    κ ≤ absoluteCharge G ∧
    (n : ℝ) * Real.log 2 * (absoluteCharge G - κ) + L * smallDefect G L ≤
      g + Real.log (1 + κ) +
        ((n : ℝ) * Real.log 2) * Real.exp (-2 * ((n : ℝ) * Real.log 2 - L)) /
          (1 - Real.exp (-2 * ((n : ℝ) * Real.log 2 - L))) := by
  classical
  let D := (n : ℝ) * Real.log 2
  let c := Real.log (1 + κ)
  let s := Real.exp (-2 * (D - L))
  let ρ := D * s / (1 - s)
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg (by norm_num))
  have hc : 0 ≤ c := Real.log_nonneg (by linarith)
  have hs : 0 < s := Real.exp_pos _
  have hs1 : s < 1 := by
    apply Real.exp_lt_one_iff.2
    dsimp [D] at *
    linarith
  have hlog : Real.log s = 2 * (L - D) := by rw [Real.log_exp]; ring
  have hterm (z : Z) :
      D * |componentMoment (G.mean z)| +
        (if G.weight z < Real.exp (-L) then L else 0) *
          (1 - |componentMoment (G.mean z)|) - ρ ≤
        -Real.log (G.weight z) + c := by
    have hw := weight_le_one G z
    have hd : 0 ≤ -Real.log (G.weight z) :=
      neg_nonneg.mpr (Real.log_nonpos (G.weight_pos z).le hw)
    have ht0 := abs_nonneg (componentMoment (G.mean z))
    have ht1 := componentMoment_abs_le_one (G.mean z) (G.mean_bound z)
    by_cases hsmall : G.weight z < Real.exp (-L)
    · simp only [if_pos hsmall]
      have hdL : L ≤ -Real.log (G.weight z) := by
        have hh := Real.log_le_log (G.weight_pos z) hsmall.le
        rw [Real.log_exp] at hh
        linarith
      exact log_cutoff_chord hD hL hLD.le hs hs1 ht0 ht1 hlog.ge
        (by linarith) (component_log_capacity G hκ z)
    · simp only [if_neg hsmall, zero_mul, add_zero]
      simpa only [zero_mul, add_zero] using
        (log_cutoff_chord hD (show (0 : ℝ) ≤ 0 by rfl) hD hs hs1 ht0 ht1
          (by linarith : 2 * (0 - D) ≤ Real.log s) (by linarith : 0 ≤
            -Real.log (G.weight z) + c) (component_log_capacity G hκ z))
  have hweighted :
      D * absoluteCharge G + L * smallDefect G L - ρ ≤
        shannonEntropy G.weight + c := by
    have hh := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset Z)) =>
      mul_le_mul_of_nonneg_left (hterm z) (G.weight_pos z).le)
    have hleft :
        (∑ z, G.weight z * (D * |componentMoment (G.mean z)| +
          (if G.weight z < Real.exp (-L) then L else 0) *
            (1 - |componentMoment (G.mean z)|) - ρ)) =
        D * absoluteCharge G + L * smallDefect G L - ρ := by
      calc
        _ = ∑ z, (D * (G.weight z * |componentMoment (G.mean z)|) +
            L * (if G.weight z < Real.exp (-L) then
              G.weight z * (1 - |componentMoment (G.mean z)|) else 0) -
                ρ * G.weight z) := by
          apply Finset.sum_congr rfl
          intro z _
          split_ifs <;> ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
            G.weight_sum, mul_one]
          rfl
    have hright : (∑ z, G.weight z * (-Real.log (G.weight z) + c)) =
        shannonEntropy G.weight + c := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, G.weight_sum, one_mul]
      congr 1
      unfold shannonEntropy
      apply Finset.sum_congr rfl
      intro z _
      unfold Real.negMulLog
      ring
    rw [hleft, hright] at hh
    exact hh
  have hn : 0 < n := by
    by_contra hh
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hh
    simp only [hn0, Nat.cast_zero, zero_mul] at hLD
    linarith
  constructor
  · calc
      κ = ∑ z, G.weight z * componentMoment (G.mean z) :=
        (generator_parity_moment G hn).symm
      _ ≤ absoluteCharge G := by
        apply Finset.sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left (le_abs_self _) (G.weight_pos z).le
  change D * (absoluteCharge G - κ) + L * smallDefect G L ≤ g + c + ρ
  change shannonEntropy G.weight ≤ D * κ + g at hH
  linarith

/-- Labels retained above the logarithmic weight threshold. -/
def largeLabels {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (L : ℝ) : Finset Z :=
  Finset.univ.filter (fun z => Real.exp (-L) ≤ G.weight z)

/-- The unnormalized density of retained sources relative to the fair law. -/
def largeDensity {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (L : ℝ) (x : Fin n → Fin 2) : ℝ :=
  ∑ z ∈ largeLabels G L, G.weight z *
    windowLaw (fun i b => 1 + G.mean z i * σ b) x

local notation "Q" => (fun {n : ℕ} (m : Fin n → ℝ) => ∏ i, (1 + |m i|))
local notation "F" => (fun {n : ℕ} (m : Fin n → ℝ) =>
  windowLaw (fun (i : Fin n) (b : Fin 2) => 1 + m i * σ b))
local notation "flip" => (fun {n : ℕ} (x : Fin n → Fin 2) (i : Fin n) =>
  Function.update x i (Equiv.swap (0 : Fin 2) 1 (x i)))

private theorem large_mass_le_one {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (L : ℝ) :
    (∑ z ∈ largeLabels G L, G.weight z) ≤ 1 := by
  classical
  rw [← G.weight_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun z _ _ => (G.weight_pos z).le)

private theorem large_card_le {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (L : ℝ) :
    ((largeLabels G L).card : ℝ) ≤ Real.exp L := by
  classical
  have hh : ((largeLabels G L).card : ℝ) * Real.exp (-L) ≤ 1 := by
    calc
      _ = ∑ z ∈ largeLabels G L, Real.exp (-L) := by simp
      _ ≤ ∑ z ∈ largeLabels G L, G.weight z :=
        Finset.sum_le_sum (fun z hz => (Finset.mem_filter.mp hz).2)
      _ ≤ 1 := large_mass_le_one G L
  have hmul := mul_le_mul_of_nonneg_right hh (Real.exp_pos L).le
  rw [mul_assoc, ← Real.exp_add] at hmul
  simp only [neg_add_cancel, Real.exp_zero, mul_one, one_mul] at hmul
  exact hmul

private theorem density_mode_capacity {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (hκ : 0 ≤ κ) (z : Z) :
    G.weight z * Q (G.mean z) ≤ 1 + κ := by
  have hh := mode_capacity G hκ z
  rw [mode_mass, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hh
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have ht := mul_le_mul_of_nonneg_right hh hp.le
  rw [mul_assoc, div_mul_cancel₀ _ hp.ne'] at ht
  have heq : (2 : ℝ)⁻¹ ^ n * ((1 + κ) * 2 ^ n) = 1 + κ := by
    calc
      _ = ((2 : ℝ)⁻¹ ^ n * 2 ^ n) * (1 + κ) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  rw [mul_assoc, heq] at ht
  exact ht

private theorem log_coordinate_chord {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    u * Real.log 2 ≤ Real.log (1 + u) := by
  have hh := strictConcaveOn_log_Ioi.concaveOn.2
    (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 2 by norm_num)
    (show 0 ≤ 1 - u by linarith) hu (by ring : (1 - u) + u = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hh
  have heq : (1 - u) * 1 + u * 2 = 1 + u := by ring
  simpa only [heq] using hh

private theorem large_coordinate_budget {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (hκ : 0 ≤ κ) (L : ℝ) (z : Z)
    (hz : z ∈ largeLabels G L) :
    (∑ i, |G.mean z i|) ≤ (L + Real.log (1 + κ)) / Real.log 2 := by
  have hQ : 0 < Q (G.mean z) := Finset.prod_pos (fun i _ => by positivity)
  have hlog := Real.log_le_log (mul_pos (G.weight_pos z) hQ)
    (density_mode_capacity G hκ z)
  rw [Real.log_mul (G.weight_pos z).ne' hQ.ne',
    Real.log_prod (fun i _ => by positivity)] at hlog
  have hw : -L ≤ Real.log (G.weight z) := by
    have hh := Real.log_le_log (Real.exp_pos (-L)) (Finset.mem_filter.mp hz).2
    rw [Real.log_exp] at hh
    exact hh
  have hc : (∑ i, |G.mean z i|) * Real.log 2 ≤
      ∑ i, Real.log (1 + |G.mean z i|) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ =>
      log_coordinate_chord (abs_nonneg _) (G.mean_bound z i))
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  linarith

private theorem large_moment_bound {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (hκ : 0 ≤ κ) (L : ℝ) (z : Z)
    (hz : z ∈ largeLabels G L) :
    |componentMoment (G.mean z)| ≤
      ((1 + κ) * (2 : ℝ)⁻¹ ^ n * Real.exp L) ^ 2 := by
  let q := productChannel (G.mean z) (mode (G.mean z))
  have hq : 0 ≤ q := productChannel_nonneg _ (G.mean_bound z) _
  have hw : 1 ≤ G.weight z * Real.exp L := by
    have hh := mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hz).2
      (Real.exp_pos L).le
    rw [← Real.exp_add] at hh
    simpa using hh
  have hh := mul_le_mul_of_nonneg_right (mode_capacity G hκ z) (Real.exp_pos L).le
  have hqcap : q ≤ (1 + κ) * (2 : ℝ)⁻¹ ^ n * Real.exp L := by
    have hnonneg := mul_nonneg hq (sub_nonneg.mpr hw)
    dsimp [q] at hnonneg ⊢
    nlinarith
  have hK : 0 ≤ (1 + κ) * (2 : ℝ)⁻¹ ^ n * Real.exp L := by positivity
  have hm := moment_le_mode_sq (G.mean z)
  change |componentMoment (G.mean z)| ≤ q ^ 2 at hm
  nlinarith

private theorem cutoff_mass_error {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (hκ : 0 ≤ κ) (L g : ℝ)
    (hL : 0 < L) (hLD : L < (n : ℝ) * Real.log 2)
    (hH : shannonEntropy G.weight ≤ (n : ℝ) * Real.log 2 * κ + g) :
    |(∑ z ∈ largeLabels G L, G.weight z) - (1 - κ)| ≤
      (g + Real.log (1 + κ) +
        ((n : ℝ) * Real.log 2) * Real.exp (-2 * ((n : ℝ) * Real.log 2 - L)) /
          (1 - Real.exp (-2 * ((n : ℝ) * Real.log 2 - L)))) /
            ((n : ℝ) * Real.log 2) +
      (g + Real.log (1 + κ) +
        ((n : ℝ) * Real.log 2) * Real.exp (-2 * ((n : ℝ) * Real.log 2 - L)) /
          (1 - Real.exp (-2 * ((n : ℝ) * Real.log 2 - L)))) / L +
      ((1 + κ) * (2 : ℝ)⁻¹ ^ n * Real.exp L) ^ 2 := by
  classical
  let D := (n : ℝ) * Real.log 2
  let B := g + Real.log (1 + κ) + D * Real.exp (-2 * (D - L)) /
    (1 - Real.exp (-2 * (D - L)))
  let η := ((1 + κ) * (2 : ℝ)⁻¹ ^ n * Real.exp L) ^ 2
  let p := ∑ z ∈ largeLabels G L, G.weight z
  let T := absoluteCharge G
  let E := smallDefect G L
  let A := ∑ z ∈ largeLabels G L, G.weight z * |componentMoment (G.mean z)|
  have hD : 0 < D := hL.trans hLD
  have hT := (entropy_truncation_coercivity G hκ L g hL.le hLD hH).1
  have hco := (entropy_truncation_coercivity G hκ L g hL.le hLD hH).2
  change D * (T - κ) + L * E ≤ B at hco
  have hE : 0 ≤ E := by
    apply Finset.sum_nonneg
    intro z _
    split_ifs
    · exact mul_nonneg (G.weight_pos z).le
        (sub_nonneg.mpr (componentMoment_abs_le_one _ (G.mean_bound z)))
    · rfl
  have hA : 0 ≤ A := Finset.sum_nonneg (fun z _ =>
    mul_nonneg (G.weight_pos z).le (abs_nonneg _))
  have hAη : A ≤ η := by
    calc
      _ ≤ ∑ z ∈ largeLabels G L, G.weight z * η :=
        Finset.sum_le_sum (fun z hz => mul_le_mul_of_nonneg_left
          (large_moment_bound G hκ L z hz) (G.weight_pos z).le)
      _ = p * η := by rw [Finset.sum_mul]
      _ ≤ η := mul_le_of_le_one_left (sq_nonneg _) (large_mass_le_one G L)
  have hp : 1 - p = T - A + E := by
    have heq (z : Z) :
        G.weight z - (if Real.exp (-L) ≤ G.weight z then G.weight z else 0) =
          G.weight z * |componentMoment (G.mean z)| -
          (if Real.exp (-L) ≤ G.weight z then
            G.weight z * |componentMoment (G.mean z)| else 0) +
          (if G.weight z < Real.exp (-L) then
            G.weight z * (1 - |componentMoment (G.mean z)|) else 0) := by
      by_cases hz : Real.exp (-L) ≤ G.weight z
      · simp [hz, not_lt.mpr hz]
      · simp [hz, lt_of_not_ge hz]; ring
    have hh := congrArg (fun f : Z → ℝ => ∑ z, f z) (funext heq)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hh
    simpa [p, T, A, E, largeLabels, absoluteCharge, smallDefect, G.weight_sum,
      Finset.sum_filter] using hh
  have hTB : T - κ ≤ B / D := (le_div_iff₀ hD).2 (by
    have hn := mul_nonneg hL.le hE
    nlinarith [hco])
  have hEB : E ≤ B / L := (le_div_iff₀ hL).2 (by
    have hn := mul_nonneg hD.le (sub_nonneg.mpr hT)
    nlinarith [hco])
  change |p - (1 - κ)| ≤ B / D + B / L + η
  apply abs_le.mpr
  constructor <;> linarith

private theorem density_eq_scaled_channel {n : ℕ} (m : Fin n → ℝ)
    (x : Fin n → Fin 2) : F m x = (2 : ℝ) ^ n * productChannel m x := by
  change (∏ i, (1 + m i * σ (x i))) =
    (2 : ℝ) ^ n * ∏ i, (1 + m i * σ (x i)) / 2
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp

private theorem large_density_mean {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (L : ℝ) :
    (𝔼 x : Fin n → Fin 2, largeDensity G L x) =
      ∑ z ∈ largeLabels G L, G.weight z := by
  classical
  have hnorm (z : Z) : (∑ x : Fin n → Fin 2, productChannel (G.mean z) x) = 1 := by
    apply windowLaw_sum_eq_one
    intro i
    rw [Fin.sum_univ_two]
    norm_num [paritySign]
    ring
  rw [Fintype.expect_eq_sum_div_card]
  simp only [largeDensity, density_eq_scaled_channel]
  rw [Finset.sum_comm]
  have hcard : (Fintype.card (Fin n → Fin 2) : ℝ) = (2 : ℝ) ^ n := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [hcard, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.mul_sum, ← Finset.mul_sum, hnorm z]
  field_simp

private theorem large_density_cap {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (L : ℝ) (x : Fin n → Fin 2) :
    largeDensity G L x ≤ 1 + κ * ∏ i, σ (x i) := by
  classical
  have hnonneg (z : Z) : 0 ≤ G.weight z * F (G.mean z) x := by
    rw [density_eq_scaled_channel]
    exact mul_nonneg (G.weight_pos z).le (mul_nonneg (by positivity)
      (productChannel_nonneg _ (G.mean_bound z) _))
  calc
    _ ≤ ∑ z, G.weight z * F (G.mean z) x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun z _ _ => hnonneg z)
    _ = (2 : ℝ) ^ n * parityMass κ x := by
      simp_rw [density_eq_scaled_channel]
      rw [← G.exact_mass x, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by
      dsimp [parityMass]
      rw [← mul_assoc, ← mul_pow]
      norm_num

private theorem parity_flip {n : ℕ} (x : Fin n → Fin 2) (j : Fin n) :
    (∏ i, σ (flip x j i)) = -(∏ i, σ (x i)) := by
  classical
  have hsign : σ (Equiv.swap (0 : Fin 2) 1 (x j)) = -σ (x j) := by
    generalize hx : x j = b
    fin_cases b <;> norm_num [paritySign, Equiv.swap_apply_def]
  rw [← Finset.mul_prod_erase _ (fun i => σ (flip x j i)) (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ (fun i => σ (x i)) (Finset.mem_univ j)]
  simp only [Function.update_self, hsign, neg_mul]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

private theorem density_flip_bound {n : ℕ} (m : Fin n → ℝ)
    (hm : ∀ i, |m i| ≤ 1) (x : Fin n → Fin 2) (j : Fin n) :
    |F m x - F m (flip x j)| ≤ 2 * Q m * |m j| := by
  classical
  let E := ∏ i ∈ Finset.univ.erase j, (1 + m i * σ (x i))
  have hsign : σ (Equiv.swap (0 : Fin 2) 1 (x j)) = -σ (x j) := by
    generalize hx : x j = b
    fin_cases b <;> norm_num [paritySign, Equiv.swap_apply_def]
  have hsabs : |σ (x j)| = 1 := by
    generalize hx : x j = b
    fin_cases b <;> norm_num [paritySign]
  have hfactor (i : Fin n) : 0 ≤ 1 + m i * σ (x i) ∧
      1 + m i * σ (x i) ≤ 1 + |m i| := by
    have hh := abs_le.mp (hm i)
    generalize hx : x i = b
    fin_cases b <;> norm_num [paritySign]
    · constructor <;> linarith [neg_le_abs (m i)]
    · constructor <;> linarith [le_abs_self (m i)]
  have hE : 0 ≤ E := Finset.prod_nonneg (fun i _ => (hfactor i).1)
  have hEQ : E ≤ Q m := by
    calc
      _ ≤ ∏ i ∈ Finset.univ.erase j, (1 + |m i|) :=
        Finset.prod_le_prod (fun i _ => (hfactor i).1) (fun i _ => (hfactor i).2)
      _ ≤ Q m := Finset.prod_le_prod_of_subset_of_one_le (Finset.erase_subset _ _)
        (fun i _ => by positivity) (fun i _ _ => by linarith [abs_nonneg (m i)])
  have hdiff : F m x - F m (flip x j) = 2 * m j * σ (x j) * E := by
    change (∏ i, (1 + m i * σ (x i))) -
      (∏ i, (1 + m i * σ (flip x j i))) = _
    rw [← Finset.mul_prod_erase _ (fun i => 1 + m i * σ (x i)) (Finset.mem_univ j),
      ← Finset.mul_prod_erase _ (fun i => 1 + m i * σ (flip x j i))
        (Finset.mem_univ j)]
    have heq : (∏ i ∈ Finset.univ.erase j, (1 + m i * σ (flip x j i))) = E := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [Function.update_of_ne (Finset.mem_erase.mp hi).1]
    rw [heq]
    simp only [Function.update_self, hsign]
    dsimp [E]
    ring
  rw [hdiff, abs_mul, abs_mul, abs_mul, hsabs, abs_of_nonneg hE]
  norm_num
  nlinarith [mul_nonneg (abs_nonneg (m j)) (sub_nonneg.mpr hEQ)]

private theorem large_flip_average_bound {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (hκ : 0 ≤ κ) (L : ℝ) (hL : 0 ≤ L) (hn : 0 < n)
    (x : Fin n → Fin 2) :
    |largeDensity G L x - (∑ j, largeDensity G L (flip x j)) / n| ≤
      2 * (1 + κ) * Real.exp L * (L + Real.log (1 + κ)) /
        ((n : ℝ) * Real.log 2) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbudget : 0 ≤ (L + Real.log (1 + κ)) / Real.log 2 :=
    div_nonneg (add_nonneg hL (Real.log_nonneg (by linarith))) hlog2.le
  have hdiff (j : Fin n) :
      |largeDensity G L x - largeDensity G L (flip x j)| ≤
        ∑ z ∈ largeLabels G L, 2 * G.weight z * Q (G.mean z) * |G.mean z j| := by
    rw [largeDensity, largeDensity, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ z ∈ largeLabels G L,
          |G.weight z * F (G.mean z) x - G.weight z * F (G.mean z) (flip x j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro z hz
        rw [← mul_sub, abs_mul, abs_of_pos (G.weight_pos z)]
        have hh := mul_le_mul_of_nonneg_left
          (density_flip_bound (G.mean z) (G.mean_bound z) x j) (G.weight_pos z).le
        nlinarith [hh]
  have hsum : (∑ j, |largeDensity G L x - largeDensity G L (flip x j)|) ≤
      2 * (1 + κ) * Real.exp L * (L + Real.log (1 + κ)) / Real.log 2 := by
    calc
      _ ≤ ∑ j, ∑ z ∈ largeLabels G L,
          2 * G.weight z * Q (G.mean z) * |G.mean z j| :=
        Finset.sum_le_sum (fun j _ => hdiff j)
      _ = ∑ z ∈ largeLabels G L, 2 * (G.weight z * Q (G.mean z)) *
          ∑ j, |G.mean z j| := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ z ∈ largeLabels G L,
          2 * (1 + κ) * ((L + Real.log (1 + κ)) / Real.log 2) := by
        apply Finset.sum_le_sum
        intro z hz
        exact mul_le_mul (by nlinarith [density_mode_capacity G hκ z])
          (large_coordinate_budget G hκ L z hz)
          (Finset.sum_nonneg (fun j _ => abs_nonneg _)) (by positivity)
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hh := mul_le_mul_of_nonneg_right (large_card_le G L)
          (mul_nonneg (by positivity : 0 ≤ 2 * (1 + κ)) hbudget)
        calc
          _ ≤ Real.exp L * (2 * (1 + κ) *
              ((L + Real.log (1 + κ)) / Real.log 2)) := hh
          _ = _ := by ring
  have hidentity : largeDensity G L x - (∑ j, largeDensity G L (flip x j)) / n =
      (∑ j, (largeDensity G L x - largeDensity G L (flip x j))) / n := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  rw [hidentity, abs_div, abs_of_pos hnR]
  apply (div_le_iff₀ hnR).2
  have hh := (Finset.abs_sum_le_sum_abs _ _).trans hsum
  convert hh using 1
  field_simp

/-- The entropy-selected large-source mixture is uniformly close to the
constant density `1 - κ` under the fair law, for the same exact generator. -/
theorem entropy_cutoff_parity_transfer {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (hκ : 0 ≤ κ) (L g : ℝ)
    (hL : 0 < L) (hLD : L < (n : ℝ) * Real.log 2)
    (hH : shannonEntropy G.weight ≤ (n : ℝ) * Real.log 2 * κ + g) :
    let D := (n : ℝ) * Real.log 2
    let B := g + Real.log (1 + κ) + D * Real.exp (-2 * (D - L)) /
      (1 - Real.exp (-2 * (D - L)))
    let η := ((1 + κ) * (2 : ℝ)⁻¹ ^ n * Real.exp L) ^ 2
    let ε := 2 * (1 + κ) * Real.exp L * (L + Real.log (1 + κ)) / D
    (𝔼 x : Fin n → Fin 2, |largeDensity G L x - (1 - κ)|) ≤
      B / D + B / L + η + 2 * ε := by
  classical
  dsimp only
  let D := (n : ℝ) * Real.log 2
  let B := g + Real.log (1 + κ) + D * Real.exp (-2 * (D - L)) /
    (1 - Real.exp (-2 * (D - L)))
  let η := ((1 + κ) * (2 : ℝ)⁻¹ ^ n * Real.exp L) ^ 2
  let ε := 2 * (1 + κ) * Real.exp L * (L + Real.log (1 + κ)) / D
  let a := 1 - κ
  have hn : 0 < n := by
    by_contra hh
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hh
    simp only [hn0, Nat.cast_zero, zero_mul] at hLD
    linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : 0 < D := hL.trans hLD
  have hε : 0 ≤ ε := by
    exact div_nonneg (mul_nonneg (by positivity)
      (add_nonneg hL.le (Real.log_nonneg (by linarith)))) hD.le
  have hupper (x : Fin n → Fin 2) : largeDensity G L x ≤ a + ε := by
    have hsquare : (∏ i, σ (x i)) ^ 2 = 1 := by
      rw [← Finset.prod_pow]
      apply Finset.prod_eq_one
      intro i _
      generalize hx : x i = b
      fin_cases b <;> norm_num [paritySign]
    rcases sq_eq_one_iff.mp hsquare with hx | hx
    · have havg : (∑ j, largeDensity G L (flip x j)) / n ≤ a := by
        apply (div_le_iff₀ hnR).2
        calc
          _ ≤ ∑ _j : Fin n, a := by
            apply Finset.sum_le_sum
            intro j _
            have hp := parity_flip x j
            rw [hx] at hp
            have hh := large_density_cap G L (flip x j)
            rw [hp] at hh
            dsimp [a]
            linarith [hh]
          _ = a * n := by simp [mul_comm]
      have hf := (abs_le.mp (large_flip_average_bound G hκ L hL.le hn x)).2
      change largeDensity G L x - (∑ j, largeDensity G L (flip x j)) / n ≤ ε at hf
      linarith
    · have hh := large_density_cap G L x
      rw [hx] at hh
      dsimp [a]
      linarith [hh]
  have habs (x : Fin n → Fin 2) : |largeDensity G L x - a| ≤
      a - largeDensity G L x + 2 * ε := by
    apply abs_le.mpr
    constructor <;> linarith [hupper x]
  have hexp : (𝔼 x : Fin n → Fin 2, |largeDensity G L x - a|) ≤
      a - (∑ z ∈ largeLabels G L, G.weight z) + 2 * ε := by
    calc
      _ ≤ 𝔼 x : Fin n → Fin 2, (a - largeDensity G L x + 2 * ε) :=
        Finset.expect_le_expect (fun x _ => habs x)
      _ = _ := by
        rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
          Fintype.expect_const, Fintype.expect_const, large_density_mean]
  have hmass := cutoff_mass_error G hκ L g hL hLD hH
  change |(∑ z ∈ largeLabels G L, G.weight z) - a| ≤ B / D + B / L + η at hmass
  change (𝔼 x : Fin n → Fin 2, |largeDensity G L x - a|) ≤
    B / D + B / L + η + 2 * ε
  linarith [(abs_le.mp hmass).1]
end
end D5.S3.Entropy.ProductGenerator.EntropyTruncation
