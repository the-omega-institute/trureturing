/- GID: D5/S3/Analytic/Oscillation/MontgomeryWindow
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/MontgomeryWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Averaged Montgomery lower bounds give mean-square mass in logarithmic cosine windows. -/

import D5.S3.Analytic.Fourier.AngularFejerKernel
import D5.S3.Analytic.Laplace.QuantitativeFejerBoundary.DampedIdentity
import D5.S3.Analytic.Oscillation.OrdinateCounting
import D5.S3.Weil.ZetaCore.ExplicitFormula

/-! Finite cosine sums acquire logarithmic window mass from averaged pair correlation. -/

namespace D5.S3.Analytic.Oscillation.MontgomeryWindow

open D5.S3.Analytic.Oscillation.OrdinateCounting
open Set Filter MeasureTheory
open scoped Topology BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

noncomputable def hardCos (S : Spectrum) (M y : ℝ) : ℝ :=
  ∑ j ∈ S.cut M, (S.mult j : ℝ) * Real.cos (S.gamma j * y)

noncomputable def montgomery (S : Spectrum) (α T : ℝ) : ℝ :=
  2 * Real.pi / (T * Real.log T) *
    ∑ j ∈ S.cut T, ∑ k ∈ S.cut T,
      (S.mult j : ℝ) * (S.mult k : ℝ) *
        Real.cos (α * Real.log T * (S.gamma j - S.gamma k)) *
        (4 / (4 + (S.gamma j - S.gamma k) ^ 2))

def AveragedMontgomeryLower (S : Spectrum) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop,
    2 / 3 - ε ≤ ∫ α in (17 : ℝ)..19, montgomery S α T

private def h (v : ℝ) : ℝ := Real.exp (-2 * |v|)

private lemma h_integrable : Integrable h := by
  have hi := Zeta23.EF.integrable_exp_neg_abs_half
  have hs := hi.comp_mul_left' (show (4 : ℝ) ≠ 0 by norm_num)
  have he : (fun v : ℝ => (Real.exp (-|4 * v| / 2) : ℂ)) = fun v => (h v : ℂ) := by
    funext v
    simp only [abs_mul, abs_of_pos (show (0 : ℝ) < 4 by norm_num), h]
    congr 2
    ring
  rw [he] at hs
  have hh := Complex.reCLM.integrable_comp (φ := fun v : ℝ => (h v : ℂ)) hs
  simpa only [Complex.reCLM_apply, Complex.ofReal_re] using hh

private lemma h_transform (t : ℝ) :
    (∫ v : ℝ, (h v : ℂ) * Complex.exp (-Complex.I * t * v)) =
      ((4 / (4 + t ^ 2) : ℝ) : ℂ) := by
  have he (v : ℝ) :
      (Real.exp (-|4 * v| / 2) : ℂ) *
        Complex.exp (-Complex.I * ((t / 4 : ℝ) : ℂ) * (4 * v : ℝ)) =
      (h v : ℂ) * Complex.exp (-Complex.I * t * v) := by
    simp only [abs_mul, abs_of_pos (show (0 : ℝ) < 4 by norm_num), h]
    congr 1
    · congr 2; ring
    · congr 1; push_cast; ring
  have hi := Measure.integral_comp_mul_left
    (fun u : ℝ => (Real.exp (-|u| / 2) : ℂ) *
      Complex.exp (-Complex.I * ((t / 4 : ℝ) : ℂ) * u)) (4 : ℝ)
  simp_rw [he] at hi
  rw [Zeta23.EF.integral_exp_neg_abs_half] at hi
  norm_num only [abs_of_pos (show (0 : ℝ) < 4 by norm_num), smul_eq_mul] at hi
  rw [hi, RCLike.real_smul_eq_coe_mul]
  push_cast
  have hd : (4 : ℂ) + (t : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show (4 : ℝ) + t ^ 2 ≠ 0 by positivity)
  field_simp

private lemma h_cosine (t y : ℝ) :
    (∫ v : ℝ, h v * Real.cos (t * (y - v))) =
      (4 / (4 + t ^ 2)) * Real.cos (t * y) := by
  have hc := D5.S3.Analytic.Fourier.AngularFejerKernel.cosine_convolution
    h_integrable h_transform t y
  calc
    _ = ∫ u : ℝ, h (y - u) * Real.cos (t * (y - (y - u))) :=
      (integral_sub_left_eq_self
        (fun v : ℝ => h v * Real.cos (t * (y - v))) volume y).symm
    _ = _ := by simpa only [sub_sub_cancel, mul_comm] using hc

private lemma h_mass : (∫ v : ℝ, h v) = 1 := by
  simpa using h_cosine 0 0

lemma hardCos_continuous (S : Spectrum) (M : ℝ) : Continuous (hardCos S M) := by
  have he : hardCos S M = fun y =>
      -D5.S3.Analytic.Laplace.QuantitativeFejerBoundary.polePolynomial S (M / 2) y := by
    funext y
    simp only [D5.S3.Analytic.Laplace.QuantitativeFejerBoundary.polePolynomial,
      show 2 * (M / 2) = M by ring, neg_neg, hardCos]
  rw [he]
  exact (D5.S3.Analytic.Laplace.QuantitativeFejerBoundary.polePolynomial_continuous S (M / 2)).neg

private lemma hardCos_bound (S : Spectrum) (M y : ℝ) : |hardCos S M y| ≤ S.N M := by
  simpa only [D5.S3.Analytic.Laplace.QuantitativeFejerBoundary.polePolynomial,
    show 2 * (M / 2) = M by ring, abs_neg, hardCos] using
    D5.S3.Analytic.Laplace.QuantitativeFejerBoundary.polePolynomial_bound S (M / 2) y

private lemma h_mul_cos_integrable (t y : ℝ) :
    Integrable (fun v : ℝ => h v * Real.cos (t * (y - v))) :=
  h_integrable.mul_bdd (c := 1) (by fun_prop)
    (Eventually.of_forall fun _ => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)

private def pairCos (t y : ℝ) : ℝ :=
  (4 / (4 + t ^ 2)) * Real.cos (t * y)

private def sumFrequency (S : Spectrum) (M y : ℝ) : ℝ :=
  ∑ j ∈ S.cut M, ∑ k ∈ S.cut M,
    (S.mult j : ℝ) * (S.mult k : ℝ) * pairCos (S.gamma j + S.gamma k) y

private lemma smoothed_square (S : Spectrum) (M y : ℝ) :
    2 * (∫ v : ℝ, h v * hardCos S M (y - v) ^ 2) =
      (∑ j ∈ S.cut M, ∑ k ∈ S.cut M,
        (S.mult j : ℝ) * (S.mult k : ℝ) * pairCos (S.gamma j - S.gamma k) y) +
      sumFrequency S M y := by
  classical
  have hp (z : ℝ) : 2 * hardCos S M z ^ 2 =
      ∑ j ∈ S.cut M, ∑ k ∈ S.cut M,
        (S.mult j : ℝ) * (S.mult k : ℝ) *
          (Real.cos ((S.gamma j - S.gamma k) * z) +
           Real.cos ((S.gamma j + S.gamma k) * z)) := by
    simp only [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    simp only [show ∀ a b c d : ℝ, a * b + c * d + (a * b - c * d) = 2 * a * b
      from fun _ _ _ _ => by ring]
    simp only [hardCos, sq, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hi (j k : S.index) : Integrable (fun v : ℝ =>
      (S.mult j : ℝ) * (S.mult k : ℝ) *
        (h v * Real.cos ((S.gamma j - S.gamma k) * (y - v)) +
         h v * Real.cos ((S.gamma j + S.gamma k) * (y - v)))) :=
    ((h_mul_cos_integrable _ _).add (h_mul_cos_integrable _ _)).const_mul _
  calc
    _ = ∫ v : ℝ, h v * (2 * hardCos S M (y - v) ^ 2) := by
      rw [← integral_const_mul]
      congr 1
      funext v
      ring
    _ = ∫ v : ℝ, ∑ j ∈ S.cut M, ∑ k ∈ S.cut M,
        (S.mult j : ℝ) * (S.mult k : ℝ) *
          (h v * Real.cos ((S.gamma j - S.gamma k) * (y - v)) +
           h v * Real.cos ((S.gamma j + S.gamma k) * (y - v))) := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [hp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi j k))]
      simp_rw [integral_finsetSum _ (fun k _ => hi _ k), integral_const_mul,
        integral_add (h_mul_cos_integrable _ _) (h_mul_cos_integrable _ _), h_cosine]
      simp only [sumFrequency, pairCos, mul_add, Finset.sum_add_distrib]

private lemma montgomery_normalization (S : Spectrum) {M : ℝ} (hM : 1 < M) (y : ℝ) :
    (∑ j ∈ S.cut M, ∑ k ∈ S.cut M,
      (S.mult j : ℝ) * (S.mult k : ℝ) * pairCos (S.gamma j - S.gamma k) y) =
      M * Real.log M / (2 * Real.pi) * montgomery S (y / Real.log M) M := by
  classical
  have hL : Real.log M ≠ 0 := (Real.log_pos hM).ne'
  have hM0 : M ≠ 0 := (zero_lt_one.trans hM).ne'
  unfold montgomery pairCos
  rw [div_mul_cancel₀ y hL]
  have hc : M * Real.log M / (2 * Real.pi) *
      (2 * Real.pi / (M * Real.log M)) = 1 := by field_simp
  rw [← mul_assoc, hc, one_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_comm (S.gamma j - S.gamma k) y]
  ring

private lemma montgomery_continuous (S : Spectrum) (M : ℝ) :
    Continuous (fun α => montgomery S α M) := by
  classical
  unfold montgomery
  fun_prop

private lemma difference_window (S : Spectrum) {M : ℝ} (hM : 1 < M) :
    (∫ y in (17 * Real.log M)..(19 * Real.log M),
      M * Real.log M / (2 * Real.pi) * montgomery S (y / Real.log M) M) =
      M * Real.log M ^ 2 / (2 * Real.pi) *
        (∫ α in (17 : ℝ)..19, montgomery S α M) := by
  rw [intervalIntegral.integral_const_mul]
  have hh := intervalIntegral.smul_integral_comp_mul_right
    (fun y => montgomery S (y / Real.log M) M) (a := 17) (b := 19) (Real.log M)
  simp only [smul_eq_mul, mul_div_cancel_right₀ _ (Real.log_pos hM).ne'] at hh
  have hL := (Real.log_pos hM).ne'
  calc
    _ = (M * Real.log M / (2 * Real.pi)) *
        (Real.log M * ∫ α in (17 : ℝ)..19, montgomery S α M) := by rw [hh]
    _ = _ := by ring

private def crossBudget (S : Spectrum) (M : ℝ) : ℝ :=
  ∑ j ∈ S.cut M, ∑ k ∈ S.cut M,
    (S.mult j : ℝ) * (S.mult k : ℝ) * (4 / (4 + (S.gamma j + S.gamma k) ^ 2))

private lemma sumFrequency_bound (S : Spectrum) (M y : ℝ) :
    |sumFrequency S M y| ≤ crossBudget S M := by
  classical
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  dsimp only [pairCos]
  rw [← mul_assoc, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

private lemma crossBudget_split (S : Spectrum) {M R : ℝ} (hRM : R ≤ M)
    (ht : Summable (fun j : {j : S.index // R < S.gamma j} =>
      (S.mult j.val : ℝ) / S.gamma j.val ^ 2)) :
    crossBudget S M ≤ (S.N R : ℝ) ^ 2 + 8 * (S.N M : ℝ) *
      (∑' j : {j : S.index // R < S.gamma j}, (S.mult j.val : ℝ) / S.gamma j.val ^ 2) := by
  classical
  let lo (j : S.index) : ℝ := if S.gamma j ≤ R then (S.mult j : ℝ) else 0
  let hi (j : S.index) : ℝ := if R < S.gamma j then (S.mult j : ℝ) / S.gamma j ^ 2 else 0
  have hlo : (∑ j ∈ S.cut M, lo j) = (S.N R : ℝ) := by
    rw [← Finset.sum_filter]
    have he : (S.cut M).filter (fun j => S.gamma j ≤ R) = S.cut R := by
      ext j
      simp only [Finset.mem_filter, Spectrum.cut, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact and_iff_right_of_imp (fun hj => hj.trans hRM)
    rw [he, Spectrum.N, Nat.cast_sum]
  have hhi : (∑ j ∈ S.cut M, hi j) ≤
      ∑' j : {j : S.index // R < S.gamma j}, (S.mult j.val : ℝ) / S.gamma j.val ^ 2 := by
    have hh := ht.sum_le_tsum ((S.cut M).subtype (fun j => R < S.gamma j))
      (fun j _ => by positivity)
    change (∑ j ∈ S.cut M, if R < S.gamma j then (S.mult j : ℝ) / S.gamma j ^ 2 else 0) ≤ _
    rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter]
    exact hh
  have hterm (j k : S.index) :
      (S.mult j : ℝ) * (S.mult k : ℝ) * (4 / (4 + (S.gamma j + S.gamma k) ^ 2)) ≤
        lo j * lo k + 4 * hi j * (S.mult k : ℝ) + 4 * (S.mult j : ℝ) * hi k := by
    have hd : 0 < 4 + (S.gamma j + S.gamma k) ^ 2 := by positivity
    have hj : (4 / (4 + (S.gamma j + S.gamma k) ^ 2)) ≤ 4 / S.gamma j ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos (S.gamma_pos j))
      nlinarith [S.gamma_pos j, S.gamma_pos k]
    have hk : (4 / (4 + (S.gamma j + S.gamma k) ^ 2)) ≤ 4 / S.gamma k ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos (S.gamma_pos k))
      nlinarith [S.gamma_pos j, S.gamma_pos k]
    have h1 : 4 / (4 + (S.gamma j + S.gamma k) ^ 2) ≤ 1 := (div_le_one hd).mpr (by nlinarith)
    dsimp only [lo, hi]
    by_cases hJ : S.gamma j ≤ R <;> by_cases hK : S.gamma k ≤ R
    · simp only [hJ, hK, not_lt.mpr hJ, not_lt.mpr hK, ite_true, ite_false,
        mul_zero, zero_mul, add_zero]
      exact mul_le_of_le_one_right (by positivity) h1
    · simp only [hJ, hK, not_lt.mpr hJ, lt_of_not_ge hK, ite_true, ite_false,
        mul_zero, zero_mul, zero_add]
      convert mul_le_mul_of_nonneg_left hk
        (show (0 : ℝ) ≤ S.mult j * (S.mult k : ℝ) by positivity) using 1
      ring
    · simp only [hJ, hK, lt_of_not_ge hJ, not_lt.mpr hK, ite_true, ite_false,
        mul_zero, zero_mul, zero_add, add_zero]
      convert mul_le_mul_of_nonneg_left hj
        (show (0 : ℝ) ≤ S.mult j * (S.mult k : ℝ) by positivity) using 1
      ring
    · simp only [hJ, hK, lt_of_not_ge hJ, lt_of_not_ge hK, ite_true, ite_false,
        mul_zero, zero_add]
      have hh := mul_le_mul_of_nonneg_left hj
        (show (0 : ℝ) ≤ S.mult j * (S.mult k : ℝ) by positivity)
      have hn : 0 ≤ 4 * (S.mult j : ℝ) * ((S.mult k : ℝ) / S.gamma k ^ 2) := by positivity
      have he : (S.mult j : ℝ) * (S.mult k : ℝ) * (4 / S.gamma j ^ 2) =
          4 * ((S.mult j : ℝ) / S.gamma j ^ 2) * (S.mult k : ℝ) := by ring
      rw [he] at hh
      linarith
  calc
    _ ≤ ∑ j ∈ S.cut M, ∑ k ∈ S.cut M,
        (lo j * lo k + 4 * hi j * (S.mult k : ℝ) + 4 * (S.mult j : ℝ) * hi k) :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hterm j k))
    _ = (S.N R : ℝ) ^ 2 + 8 * (S.N M : ℝ) * (∑ j ∈ S.cut M, hi j) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hlo]
      simp only [Spectrum.N, Nat.cast_sum]
      ring
    _ ≤ _ := by gcongr

private lemma crossBudget_small (S : Spectrum) (hN : CountAsymptotic S)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℝ in atTop, crossBudget S M ≤ ε * (M * Real.log M) := by
  obtain ⟨B, hB, hcount⟩ := count_upper S hN
  obtain ⟨C, hC, htail⟩ := inverse_square_tail S hN
  have hlim : Tendsto (fun R : ℝ => 8 * B * C * (Real.log R / R)) atTop (nhds 0) := by
    simpa only [mul_zero, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero |>.const_mul (8 * B * C))
  obtain ⟨R, hR4, hRsmall⟩ := (eventually_ge_atTop (4 : ℝ)).and
    (hlim.eventually (gt_mem_nhds (half_pos hε))) |>.exists
  obtain ⟨ht, htbound⟩ := htail R hR4
  filter_upwards [hcount, eventually_ge_atTop R,
    eventually_ge_atTop (2 * (S.N R : ℝ) ^ 2 / ε),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with M hc hRM hMlarge hL hM0
  have hlow : (S.N R : ℝ) ^ 2 ≤ ε / 2 * (M * Real.log M) := by
    have hh := (div_le_iff₀ hε).mp hMlarge
    have hML : M ≤ M * Real.log M := le_mul_of_one_le_right hM0 hL
    nlinarith
  have hmain := crossBudget_split S hRM ht
  have hh : 8 * (S.N M : ℝ) *
      (∑' j : {j : S.index // R < S.gamma j}, (S.mult j.val : ℝ) / S.gamma j.val ^ 2) ≤
        ε / 2 * (M * Real.log M) := by
    calc
      _ ≤ 8 * (B * (M * Real.log M)) * (C * Real.log R / R) := by
        gcongr
      _ = (8 * B * C * (Real.log R / R)) * (M * Real.log M) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hRsmall.le (mul_nonneg hM0 (by linarith))
  linarith

private lemma h_tail {L : ℝ} (hL : 0 ≤ L) :
    (∫ v in {v : ℝ | L < |v|}, h v) = Real.exp (-2 * L) := by
  have he : {v : ℝ | L < |v|} = Iio (-L) ∪ Ioi L := by
    ext v
    simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi, lt_abs]
    constructor <;> intro hh <;> rcases hh with hh | hh
    · exact Or.inr hh
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl hh
  have hd : Disjoint (Iio (-L)) (Ioi L) := Set.disjoint_left.mpr (by
    intro v hv hw
    simp only [mem_Iio, mem_Ioi] at hv hw
    linarith)
  rw [he, setIntegral_union hd measurableSet_Ioi h_integrable.integrableOn
    h_integrable.integrableOn, ← integral_Iic_eq_integral_Iio]
  have hl : (∫ v in Iic (-L), h v) = Real.exp (-2 * L) / 2 := by
    rw [setIntegral_congr_fun measurableSet_Iic
      (show EqOn h (fun v : ℝ => Real.exp (2*v)) (Iic (-L)) from by
      intro v hv
      dsimp [h]
      rw [abs_of_nonpos (by have hv' : v ≤ -L := hv; linarith)]
      congr 1; ring), integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 2)]
    congr 2; ring
  have hr : (∫ v in Ioi L, h v) = Real.exp (-2 * L) / 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (show EqOn h (fun v : ℝ => Real.exp (-2*v)) (Ioi L) from by
      intro v hv
      dsimp [h]
      rw [abs_of_nonneg (hL.trans (le_of_lt hv))]),
      integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0)]
    ring
  rw [hl, hr]
  ring

private lemma smoothed_localization (S : Spectrum) (M : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ y in (17 * L)..(19 * L), ∫ v : ℝ, h v * hardCos S M (y - v) ^ 2) ≤
      (∫ y in (16 * L)..(20 * L), hardCos S M y ^ 2) +
        2 * L * (S.N M : ℝ) ^ 2 * Real.exp (-2 * L) := by
  let f : ℝ → ℝ := fun y => hardCos S M y ^ 2
  have hf : Continuous f := (hardCos_continuous S M).pow 2
  have hf0 (y : ℝ) : 0 ≤ f y := sq_nonneg _
  have hfB (y : ℝ) : f y ≤ (S.N M : ℝ) ^ 2 := by
    exact sq_le_sq.mpr (by
      simpa only [abs_of_nonneg (Nat.cast_nonneg (S.N M) : (0 : ℝ) ≤ ↑(S.N M))]
        using hardCos_bound S M y)
  have hab : 17 * L ≤ 19 * L := by nlinarith
  have hcd : 16 * L ≤ 20 * L := by nlinarith
  let W : ℝ := ∫ y in Icc (16 * L) (20 * L), f y
  have hW : 0 ≤ W := integral_nonneg hf0
  have hp : Integrable (fun p : ℝ × ℝ => h p.2 * f (p.1 - p.2))
      ((volume.restrict (Icc (17 * L) (19 * L))).prod volume) := by
    apply ((integrableOn_const (C := (S.N M : ℝ) ^ 2) (by simp)).mul_prod h_integrable).mono'
      (by have hc : Continuous (fun p : ℝ × ℝ => h p.2 * f (p.1 - p.2)) := by dsimp [h]; fun_prop
          exact hc.aestronglyMeasurable)
    filter_upwards [] with p
    have hh : 0 ≤ h p.2 := Real.exp_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hh (hf0 _))]
    exact (mul_le_mul_of_nonneg_left (hfB _) hh).trans_eq (mul_comm _ _)
  have hinner (v : ℝ) : (∫ y in Icc (17 * L) (19 * L), f (y - v)) ≤
      W + if L < |v| then 2 * L * (S.N M : ℝ) ^ 2 else 0 := by
    by_cases hv : L < |v|
    · rw [ite_eq_left hv]
      have hi := setIntegral_mono_on
        ((hf.comp (continuous_id.sub continuous_const)).integrableOn_Icc)
        (integrableOn_const (C := (S.N M : ℝ) ^ 2) (μ := volume)
          (s := Icc (17 * L) (19 * L)) (by simp)) measurableSet_Icc (fun y _ => hfB (y-v))
      have he : (∫ _y in Icc (17 * L) (19 * L), (S.N M : ℝ) ^ 2) =
          2 * L * (S.N M : ℝ) ^ 2 := by
        rw [setIntegral_const, Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        ring
      rw [he] at hi
      change (∫ y in Icc (17 * L) (19 * L), f (y-v)) ≤ _ at hi
      linarith
    · rw [ite_eq_right hv, add_zero]
      have hv' := abs_le.mp (not_lt.mp hv)
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
        intervalIntegral.integral_comp_sub_right,
        intervalIntegral.integral_of_le (by linarith : 17 * L - v ≤ 19 * L - v),
        ← integral_Icc_eq_integral_Ioc]
      exact setIntegral_mono_set hf.integrableOn_Icc (Eventually.of_forall hf0)
        (Eventually.of_forall (fun y hy => ⟨by linarith [hy.1, hv'.2], by linarith [hy.2, hv'.1]⟩))
  have himajor : Integrable (fun v : ℝ => h v *
      (W + if L < |v| then 2 * L * (S.N M : ℝ) ^ 2 else 0)) := by
    have hi := (h_integrable.mul_const (2 * L * (S.N M : ℝ) ^ 2)).indicator
      (isOpen_lt (f := fun _ : ℝ => L) continuous_const continuous_abs).measurableSet
    convert (h_integrable.mul_const W).add hi using 1
    funext v
    simp only [indicator_apply, Pi.add_apply, mem_ofPred_eq]
    split_ifs <;> ring
  have hpinner : Integrable (fun v : ℝ => h v * ∫ y in Icc (17 * L) (19 * L), f (y-v)) := by
    simpa only [integral_const_mul] using hp.integral_prod_right
  have hbound := integral_mono hpinner himajor
    (fun v => mul_le_mul_of_nonneg_left (hinner v) (show 0 ≤ h v from Real.exp_nonneg _))
  have hemajor : (∫ v : ℝ, h v * (W + if L < |v| then 2 * L * (S.N M : ℝ) ^ 2 else 0)) =
      W + 2 * L * (S.N M : ℝ) ^ 2 * Real.exp (-2 * L) := by
    have hi := (h_integrable.mul_const (2 * L * (S.N M : ℝ) ^ 2)).indicator
      (isOpen_lt (f := fun _ : ℝ => L) continuous_const continuous_abs).measurableSet
    have he : (fun v : ℝ => h v * (W + if L < |v| then 2 * L * (S.N M : ℝ) ^ 2 else 0)) =
        (fun v => h v * W) + {v : ℝ | L < |v|}.indicator
          (fun v => h v * (2 * L * (S.N M : ℝ) ^ 2)) := by
      funext v
      simp only [Pi.add_apply, indicator_apply, mem_ofPred_eq]
      split_ifs <;> ring
    rw [he]
    change (∫ v : ℝ, h v * W + {v : ℝ | L < |v|}.indicator
      (fun v => h v * (2 * L * (S.N M : ℝ) ^ 2)) v) = _
    rw [integral_add (h_integrable.mul_const W) hi, integral_mul_const, h_mass,
      integral_indicator
        (isOpen_lt (f := fun _ : ℝ => L) continuous_const continuous_abs).measurableSet,
      integral_mul_const, h_tail hL]
    ring
  rw [hemajor] at hbound
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    integral_integral_swap hp]
  have he : (∫ v : ℝ, ∫ y in Icc (17 * L) (19 * L), h v * f (y - v)) =
      ∫ v : ℝ, h v * ∫ y in Icc (17 * L) (19 * L), f (y-v) := by
    simp_rw [integral_const_mul]
  rw [he]
  simpa only [W, intervalIntegral.integral_of_le hcd, integral_Icc_eq_integral_Ioc, f] using hbound

private lemma leakage_small (S : Spectrum) (hN : CountAsymptotic S)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℝ in atTop,
      2 * Real.log M * (S.N M : ℝ) ^ 2 * Real.exp (-2 * Real.log M) ≤
        ε * M * Real.log M ^ 2 := by
  obtain ⟨B, hB, hcount⟩ := count_upper S hN
  have hlim : Tendsto (fun M : ℝ => (2 * B ^ 2) * (Real.log M / M)) atTop (nhds 0) := by
    simpa only [mul_zero, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul (2 * B ^ 2)
  filter_upwards [hcount, eventually_gt_atTop (1 : ℝ),
    hlim.eventually (gt_mem_nhds hε)] with M hc hM heps
  have hM0 : 0 < M := zero_lt_one.trans hM
  have hL : 0 < Real.log M := Real.log_pos hM
  have he : M ^ 2 * Real.exp (-2 * Real.log M) = 1 := by
    rw [show -2 * Real.log M = -(Real.log M + Real.log M) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_log hM0]
    field_simp
  have hh : 2 * B ^ 2 * Real.log M ≤ ε * M := by
    apply (div_le_iff₀ hM0).mp
    simpa only [mul_div_assoc] using heps.le
  calc
    _ ≤ 2 * Real.log M * (B * (M * Real.log M)) ^ 2 * Real.exp (-2 * Real.log M) := by
      gcongr
    _ = 2 * B ^ 2 * Real.log M ^ 3 * (M ^ 2 * Real.exp (-2 * Real.log M)) := by ring
    _ = 2 * B ^ 2 * Real.log M ^ 3 := by rw [he, mul_one]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg (Real.log M))]

private lemma smoothed_window_lower (S : Spectrum) (hN : CountAsymptotic S)
    (hMont : AveragedMontgomeryLower S) :
    ∀ᶠ M : ℝ in atTop,
      (1 / (16 * Real.pi)) * M * Real.log M ^ 2 ≤
        ∫ y in (17 * Real.log M)..(19 * Real.log M),
          ∫ v : ℝ, h v * hardCos S M (y-v) ^ 2 := by
  let c : ℝ := 1 / (48 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  filter_upwards [hMont (1/3) (by norm_num), crossBudget_small S hN hc,
    eventually_gt_atTop (1 : ℝ)] with M hm hx hM
  have hL := Real.log_pos hM
  have hM0 : 0 < M := zero_lt_one.trans hM
  have hsf : Continuous (sumFrequency S M) := by
    classical
    unfold sumFrequency pairCos
    fun_prop
  have hdf : Continuous (fun y : ℝ =>
      M * Real.log M / (2 * Real.pi) * montgomery S (y / Real.log M) M) :=
    ((montgomery_continuous S M).comp (continuous_id.div_const _)).const_mul _
  have heq : 2 * (∫ y in (17 * Real.log M)..(19 * Real.log M),
      ∫ v : ℝ, h v * hardCos S M (y-v) ^ 2) =
      (M * Real.log M ^ 2 / (2 * Real.pi)) *
        (∫ α in (17 : ℝ)..19, montgomery S α M) +
      (∫ y in (17 * Real.log M)..(19 * Real.log M), sumFrequency S M y) := by
    rw [← intervalIntegral.integral_const_mul]
    calc
      _ = ∫ y in (17 * Real.log M)..(19 * Real.log M),
          (M * Real.log M / (2 * Real.pi) * montgomery S (y / Real.log M) M +
            sumFrequency S M y) := by
        apply intervalIntegral.integral_congr
        intro y _
        dsimp only
        rw [smoothed_square, montgomery_normalization S hM]
      _ = _ := by
        rw [intervalIntegral.integral_add (hdf.intervalIntegrable _ _) (hsf.intervalIntegrable _ _),
          difference_window S hM]
  have hsf_lower : -(2 * Real.log M * crossBudget S M) ≤
      ∫ y in (17 * Real.log M)..(19 * Real.log M), sumFrequency S M y := by
    have hh := intervalIntegral.integral_mono_on (μ := volume)
      (by nlinarith : 17 * Real.log M ≤ 19 * Real.log M)
      (intervalIntegrable_const (c := -crossBudget S M)) (hsf.intervalIntegrable _ _)
      (fun y _ => (neg_le_of_abs_le (sumFrequency_bound S M y)))
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hh
    convert hh using 1
    ring
  have hm' : 1/3 ≤ ∫ α in (17 : ℝ)..19, montgomery S α M := by linarith
  have hmain := mul_le_mul_of_nonneg_left hm'
    (show 0 ≤ M * Real.log M ^ 2 / (2 * Real.pi) by positivity)
  have hcross := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2 * Real.log M by positivity)
  have hcoef : M * Real.log M ^ 2 / (2 * Real.pi) * (1/3) =
      8 * c * (M * Real.log M ^ 2) := by dsimp [c]; ring
  have htarget : (1 / (16 * Real.pi)) * M * Real.log M ^ 2 =
      3 * c * (M * Real.log M ^ 2) := by dsimp [c]; ring
  rw [hcoef] at hmain
  rw [htarget]
  nlinarith

/-- An averaged Montgomery lower bound forces mean-square mass in the hard cosine window. -/
theorem hard_window_lower (S : Spectrum) (hN : CountAsymptotic S)
    (hMont : AveragedMontgomeryLower S) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℝ in atTop,
      c * M * (Real.log M) ^ 2 ≤
        ∫ y in (16 * Real.log M)..(20 * Real.log M), hardCos S M y ^ 2 := by
  let c : ℝ := 1 / (32 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  filter_upwards [smoothed_window_lower S hN hMont, leakage_small S hN hc,
    eventually_gt_atTop (1 : ℝ)] with M hs he hM
  have hl := smoothed_localization S M (Real.log_pos hM).le
  have hcoef : (1 / (16 * Real.pi)) * M * Real.log M ^ 2 =
      2 * (c * M * Real.log M ^ 2) := by dsimp [c]; ring
  rw [hcoef] at hs
  linarith

end
end D5.S3.Analytic.Oscillation.MontgomeryWindow
