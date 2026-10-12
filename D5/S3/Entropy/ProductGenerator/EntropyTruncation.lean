/- GID: D5/S3/Entropy/ProductGenerator/EntropyTruncation
   generality: G
   mirror-B: D5/B/S3/Entropy/ProductGenerator/EntropyTruncation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entropy truncation for exact finite product sources of an interior parity law. -/

import D5.S3.Entropy.MaxEntropy
import D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Entropy.ProductGenerator.EntropyTruncation
noncomputable section

open D5.S3.Entropy.MaxEntropy
open D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments (paritySign)

local notation "σ" b => ((paritySign b : ℤ) : ℝ)

/-- Density of independent binary coordinates with the specified means. -/
def productChannel {n : ℕ} (m : Fin n → ℝ) (x : Fin n → Fin 2) : ℝ :=
  ∏ i, (1 + m i * σ (x i)) / 2

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

/-- The full signed product moment of a source component. -/
def componentMoment {n : ℕ} (m : Fin n → ℝ) : ℝ := ∏ i, m i

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
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hLD : L ≤ D)
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
  rw [componentMoment, Finset.abs_prod]
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
  rw [componentMoment, Finset.abs_prod, mode_mass, ← Finset.prod_pow]
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

/-- Exact generation controls both excess absolute parity charge and the
small-label defect uniformly in the finite source alphabet. -/
theorem entropy_truncation_coercivity {n : ℕ} {κ : ℝ} {Z : Type*} [Fintype Z]
    (G : ExactGenerator n κ Z) (hκ : 0 ≤ κ) (L g : ℝ)
    (hL : 0 ≤ L) (hLD : L < (n : ℝ) * Real.log 2)
    (hH : shannonEntropy G.weight ≤ (n : ℝ) * Real.log 2 * κ + g) :
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
  change D * (absoluteCharge G - κ) + L * smallDefect G L ≤ g + c + ρ
  change shannonEntropy G.weight ≤ D * κ + g at hH
  linarith

#print axioms entropy_truncation_coercivity

end
end D5.S3.Entropy.ProductGenerator.EntropyTruncation
