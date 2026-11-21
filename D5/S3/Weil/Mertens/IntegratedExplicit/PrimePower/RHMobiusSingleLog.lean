/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusSingleLog
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusSingleLog
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A single-logarithm order bound for the prime-only window residual under RH. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHMobiusWindow
import D5.S3.Weil.Mertens.Cryptids.Schoenfeld

/-! Uniform Möbius truncation with one logarithm in the order bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Chebyshev Real ArithmeticFunction MeasureTheory Set
open scoped ArithmeticFunction.Moebius
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.Mertens.IntegratedExplicit
open RHSharpActualEnvelope (abs_G_sub_normalized_actualH_le)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

/-- At each omitted degree the spectral exponent stays in the sum. A geometric bound in the
distance from the first omitted degree then combines with the smaller of two envelopes. -/
private theorem omitted_root_weight_sum_le {m : ℕ} (hm : 2 ≤ m) {u : ℝ} (hu : 0 ≤ u) :
    min ((1 + 2 * (u / (m + 1 : ℝ)))^2) ((1 + Real.log m)^2) *
      (∑ n ∈ (Finset.Icc 2 m).filter (fun n => m + 1 ≤ 2 * n),
        Real.exp (-(u * ((m + 1 : ℝ)⁻¹ - (2 * (n : ℝ))⁻¹)))) ≤
      24 * (m : ℝ) * (1 + Real.log m) := by
  let q : ℝ := (m + 1 : ℝ)
  let l : ℝ := u / q
  let L : ℝ := 1 + Real.log m
  let n₀ : ℕ := (m + 2) / 2
  let S := (Finset.Icc 2 m).filter (fun n => m + 1 ≤ 2 * n)
  let w (n : ℕ) := Real.exp (-(u * (q⁻¹ - (2 * (n : ℝ))⁻¹)))
  let A := ∑ n ∈ S, w n
  change min ((1 + 2 * l)^2) (L^2) * A ≤ 24 * (m : ℝ) * L
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0 < q := by dsimp [q]; positivity
  have hql : l * q = u := div_mul_cancel₀ _ hq.ne'
  have hl : 0 ≤ l := div_nonneg hu hq.le
  have hL : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ m by linarith)]
  have hLm : L ≤ m := by
    dsimp [L]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < m by positivity)]
  have hq_m : q ≤ (3 / 2 : ℝ) * m := by dsimp [q]; linarith
  have hA₀ : 0 ≤ A := Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _)
  have hpoint (n : ℕ) (hn : n ∈ S) :
      w n ≤ Real.exp (-(l / q * ((n - n₀ : ℕ) : ℝ))) := by
    obtain ⟨hnm, hnq⟩ := Finset.mem_filter.mp hn
    have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hnm).1
    have hn₀ : (n : ℝ) > 0 := by linarith
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hnm).2
    have hn₀n : n₀ ≤ n := by dsimp [n₀]; omega
    have hq_n₀ : q ≤ 2 * (n₀ : ℝ) := by
      dsimp [q]
      exact_mod_cast (show m + 1 ≤ 2 * n₀ by dsimp [n₀]; omega)
    have hsub : ((n - n₀ : ℕ) : ℝ) = (n : ℝ) - (n₀ : ℝ) := Nat.cast_sub hn₀n
    have hd : (n : ℝ) - (n₀ : ℝ) ≤ (n : ℝ) - q / 2 := by linarith
    have hd₀ : 0 ≤ (n : ℝ) - (n₀ : ℝ) := by rw [← hsub]; positivity
    have hnq' : (n : ℝ) ≤ q := by dsimp [q]; linarith
    have hfrac : ((n : ℝ) - (n₀ : ℝ)) / q ≤ ((n : ℝ) - q / 2) / n :=
      (div_le_div_of_nonneg_left hd₀ hn₀ hnq').trans
        (div_le_div_of_nonneg_right hd hn₀.le)
    have he : u * (q⁻¹ - (2 * (n : ℝ))⁻¹) =
        l * (((n : ℝ) - q / 2) / n) := by
      rw [← hql]
      field_simp
    apply Real.exp_le_exp.mpr
    rw [he, hsub, show l / q * ((n : ℝ) - n₀) = l * (((n : ℝ) - n₀) / q) by ring]
    exact neg_le_neg (mul_le_mul_of_nonneg_left hfrac hl)
  have hcard : (S.card : ℝ) ≤ m := by
    exact_mod_cast (show S.card ≤ m from
      (Finset.card_filter_le _ _).trans (by rw [Nat.card_Icc]; omega))
  have hA_m : A ≤ m := by
    calc
      A ≤ ∑ _n ∈ S, (1 : ℝ) := Finset.sum_le_sum fun n hn =>
        (hpoint n hn).trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
      _ ≤ _ := by simpa using hcard
  have hAgeom (hlp : 0 < l) : A ≤ 1 + q / l := by
    let b := Real.exp (-(l / q))
    have hb₀ : 0 ≤ b := Real.exp_nonneg _
    have hb₁ : b < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (div_pos hlp hq))
    have hs : A ≤ ∑ j ∈ Finset.range (m + 1), b ^ j := by
      refine (Finset.sum_le_sum hpoint).trans ?_
      refine Finset.sum_le_sum_of_injOn (fun n => n - n₀) ?_ ?_ ?_ ?_
      · intro n hn j hj hnj
        change n ∈ S at hn
        change j ∈ S at hj
        have h₁ := (Finset.mem_filter.mp hn).2
        have h₂ := (Finset.mem_filter.mp hj).2
        dsimp [n₀] at hnj
        omega
      · intro j hj
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj
        have hnm := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
        exact Finset.mem_range.mpr (by omega)
      · intro i _
        dsimp only [b]
        rw [← Real.exp_nat_mul]
        apply le_of_eq
        congr 1
        ring
      · intro i _ _
        exact pow_nonneg hb₀ _
    refine hs.trans ((?_ : (∑ j ∈ Finset.range (m + 1), b ^ j) ≤ (1 - b)⁻¹).trans ?_)
    · rw [geom_sum_eq hb₁.ne, ← neg_div_neg_eq]
      simp only [neg_sub]
      rw [← one_div]
      exact div_le_div_of_nonneg_right (sub_le_self _ (pow_nonneg hb₀ _)) (sub_pos.mpr hb₁).le
    have hv : 0 < l / q := div_pos hlp hq
    have hB : b ≤ (1 + l / q)⁻¹ := by
      dsimp [b]
      rw [Real.exp_neg]
      exact inv_anti₀ (by linarith) (by simpa only [add_comm] using Real.add_one_le_exp (l / q))
    calc
      (1 - b)⁻¹ ≤ (1 - (1 + l / q)⁻¹)⁻¹ := by
        apply inv_anti₀
        · rw [sub_pos]
          exact (inv_lt_one₀ (by linarith)).mpr (by linarith)
        · linarith
      _ = 1 + q / l := by field_simp [hlp.ne']; ring
  by_cases hh : l ≤ 1
  · have hsq : (1 + 2 * l)^2 ≤ 9 := by
      have h := pow_le_pow_left₀ (show 0 ≤ 1 + 2 * l by positivity)
        (show 1 + 2 * l ≤ 3 by linarith) 2
      norm_num at h
      exact h
    calc
      _ ≤ 9 * (m : ℝ) := mul_le_mul ((min_le_left _ _).trans hsq) hA_m hA₀ (by norm_num)
      _ ≤ _ := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ m by positivity)
          (show 0 ≤ L - 1 by linarith)]
  have hl₁ : 1 < l := lt_of_not_ge hh
  by_cases hsmall : l ≤ L
  · have hsq : (1 + 2 * l)^2 ≤ (3 * l)^2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      _ ≤ (3 * l)^2 * (1 + q / l) :=
        mul_le_mul ((min_le_left _ _).trans hsq) (hAgeom (by linarith)) hA₀ (sq_nonneg _)
      _ = 9 * l * (l + q) := by
        field_simp [show l ≠ 0 by linarith]
        ring
      _ ≤ _ := by
        have hprod : l * (l + q) ≤ L * (L + q) :=
          mul_le_mul hsmall (add_le_add_left hsmall _) (by positivity) (by linarith)
        have hb : L + q ≤ (5 / 2 : ℝ) * m := by linarith
        have hbound := hprod.trans (mul_le_mul_of_nonneg_left hb (show 0 ≤ L by linarith))
        nlinarith only [hbound, mul_nonneg (show 0 ≤ L by linarith)
          (show 0 ≤ (m : ℝ) by positivity)]
  · have hLa : L ≤ l := le_of_lt (lt_of_not_ge hsmall)
    have hdiv : q / l ≤ q / L := div_le_div_of_nonneg_left hq.le (by linarith) hLa
    calc
      _ ≤ L^2 * (1 + q / L) :=
        mul_le_mul (min_le_right _ _) ((hAgeom (by linarith)).trans (add_le_add_right hdiv _))
          hA₀ (sq_nonneg _)
      _ = L * (L + q) := by field_simp [show L ≠ 0 by linarith]
      _ ≤ _ := by
        nlinarith [mul_nonneg (show 0 ≤ L by linarith)
          (show 0 ≤ 24 * m - (L + q) by linarith)]

open ConjectureMachines.Semantics.Riemann
  (SchoenfeldPsiBound abs_psi_sub_self_le_seven_eighths_of_five_thousand_le)

private theorem global_psi_error (hRH : RiemannHypothesis) {y : ℝ} (hy : 1 ≤ y) :
    |psi y - y| ≤ ((Real.log 4 + 5) * 5000) * Real.sqrt y * (1 + Real.log y)^2 := by
  have hlog := Real.log_nonneg hy
  have hs : 1 ≤ Real.sqrt y := by simpa using Real.sqrt_le_sqrt hy
  have hC : 1 ≤ (Real.log 4 + 5) * 5000 := by
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  by_cases h : 5000 ≤ y
  · have hh := abs_psi_sub_self_le_seven_eighths_of_five_thousand_le hRH h
    unfold SchoenfeldPsiBound at hh
    refine hh.trans (mul_le_mul ?_ ?_ (sq_nonneg _) (by positivity))
    · exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    · nlinarith
  · have hp := psi_le_const_mul_self (show 0 ≤ y by linarith)
    calc
      _ ≤ psi y + y := by
        simpa [abs_of_nonneg (psi_nonneg y), abs_of_nonneg (show 0 ≤ y by linarith)] using
          (abs_sub (psi y) y)
      _ ≤ (Real.log 4 + 5) * y := by linarith
      _ ≤ (Real.log 4 + 5) * 5000 :=
        mul_le_mul_of_nonneg_left (le_of_not_ge h) (by positivity)
      _ ≤ _ := by
        calc
          _ ≤ ((Real.log 4 + 5) * 5000) * Real.sqrt y := by
            simpa using mul_le_mul_of_nonneg_left hs
              (show 0 ≤ (Real.log 4 + 5) * 5000 by positivity)
          _ ≤ _ := by
            exact le_mul_of_one_le_right (by positivity) (by nlinarith)

/-- The Schoenfeld bound transported through the actual centered root-tail integral. -/
theorem centered_chebyshev_log (hRH : RiemannHypothesis) {r u : ℝ}
    (hr : 2 ≤ r) (hu : 0 ≤ u) :
    |centered r (Real.exp u)| ≤
      (16 * ((Real.log 4 + 5) * 5000)) * (1 + u / r)^2 *
        Real.exp (((2 * r)⁻¹ - 1 / 2) * u) := by
  have hr₀ : 0 < r := by linarith
  let C : ℝ := (Real.log 4 + 5) * 5000
  let p := (2 * r)⁻¹
  let W := 4 * C * (1 + u / r)^2 * Real.exp ((p - 3 / 4) * u)
  let f (t : ℝ) := (psi (t ^ r⁻¹) - t ^ r⁻¹) / t ^ 2
  let g (v : ℝ) := Real.exp v • f (Real.exp v)
  let bound (v : ℝ) := W * Real.exp (-(1 / 4 : ℝ) * v)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hp : p ≤ 1 / 4 := by
    dsimp [p]
    have h := inv_anti₀ (by norm_num : (0 : ℝ) < 4) (show (4 : ℝ) ≤ 2 * r by linarith)
    norm_num at h ⊢
    exact h
  have hb : IntegrableOn bound (Ioi u) :=
    (integrableOn_exp_mul_Ioi (a := -(1 / 4 : ℝ)) (by norm_num) u).const_mul W
  have hdom (v : ℝ) (hv : v ∈ Ioi u) : |g v| ≤ bound v := by
    have hvu : u ≤ v := le_of_lt hv
    have hvu₀ : 0 ≤ v - u := sub_nonneg.mpr hvu
    have hv₀ : 0 ≤ v := hu.trans hvu
    have hv_r : 0 ≤ v / r := div_nonneg hv₀ hr₀.le
    have hroot : (Real.exp v) ^ r⁻¹ = Real.exp (v / r) := by
      rw [← Real.exp_mul, div_eq_mul_inv]
    have hnorm : |g v| = Real.exp (-v) * |psi (Real.exp (v / r)) - Real.exp (v / r)| := by
      dsimp only [g, f, smul_eq_mul]
      rw [hroot, Real.exp_neg, show ∀ z : ℝ, Real.exp v * (z / (Real.exp v)^2) =
        (Real.exp v)⁻¹ * z by intro z; field_simp [Real.exp_ne_zero]]
      rw [abs_mul, abs_of_pos (inv_pos.mpr (Real.exp_pos _))]
    have hroot_bound := global_psi_error hRH (Real.one_le_exp_iff.mpr hv_r)
    rw [Real.log_exp, Real.sqrt_eq_rpow, ← Real.exp_mul] at hroot_bound
    have hrate : v / r * (1 / 2) = p * v := by dsimp [p]; field_simp
    rw [hrate] at hroot_bound
    have he₀ : 0 ≤ (v - u) / 4 := by positivity
    have hshift : (v - u) / r ≤ (v - u) / 2 :=
      div_le_div_of_nonneg_left hvu₀ (by norm_num) hr
    have hprod : 1 + v / r ≤ (1 + u / r) * (1 + (v - u) / 2) := by
      have hsplit : v / r = u / r + (v - u) / r := by ring
      rw [hsplit]
      nlinarith only [hshift, mul_nonneg (div_nonneg hu hr₀.le) (show 0 ≤ (v-u)/2 by positivity)]
    have hsmall : 1 + (v - u) / 2 ≤ 2 * Real.exp ((v - u) / 4) := by
      nlinarith only [Real.add_one_le_exp ((v - u) / 4)]
    have hsq : (1 + v / r)^2 ≤ 4 * (1 + u / r)^2 * Real.exp ((v - u) / 2) := by
      have h := pow_le_pow_left₀ (show 0 ≤ 1 + v / r by positivity)
        (hprod.trans (mul_le_mul_of_nonneg_left hsmall (by positivity))) 2
      convert h using 1
      rw [show (v-u)/2 = (v-u)/4 + (v-u)/4 by ring, Real.exp_add]
      ring
    have hdecay : ((p - 1) * v + (v - u) / 2) ≤ (p - 3 / 4) * u + (-(1 / 4 : ℝ)) * v := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hp) hvu₀]
    rw [hnorm]
    calc
      _ ≤ Real.exp (-v) * (C * Real.exp (p * v) * (1 + v / r)^2) :=
        mul_le_mul_of_nonneg_left hroot_bound (Real.exp_nonneg _)
      _ ≤ Real.exp (-v) * (C * Real.exp (p * v) *
          (4 * (1 + u / r)^2 * Real.exp ((v - u) / 2))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by positivity))
          (Real.exp_nonneg _)
      _ = 4 * C * (1 + u / r)^2 * Real.exp ((p - 1) * v + (v - u) / 2) := by
        rw [Real.exp_add, show (p - 1) * v = p * v + -v by ring, Real.exp_add]
        ring
      _ ≤ bound v := by
        unfold bound W
        rw [mul_assoc (4 * C * (1 + u / r)^2), ← Real.exp_add]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdecay) (by positivity)
  have hg : IntegrableOn g (Ioi u) := by
    apply hb.mono'
    · have hf : Measurable f :=
        ((psi_mono.measurable.comp (by fun_prop)).sub (by fun_prop)).div (by fun_prop)
      exact ((Real.continuous_exp.measurable).mul
        (hf.comp Real.continuous_exp.measurable)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      simpa only [Real.norm_eq_abs] using hdom v hv
  have hi : |∫ v in Ioi u, g v| ≤ ∫ v in Ioi u, bound v := by
    refine (norm_integral_le_integral_norm (f := g)).trans ?_
    apply integral_mono_ae hg.norm hb
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    simpa only [Real.norm_eq_abs] using hdom v hv
  have hvalue : (∫ v in Ioi u, bound v) = W * (4 * Real.exp (-(1 / 4 : ℝ) * u)) := by
    unfold bound
    rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num)]
    ring
  unfold centered
  change |Real.sqrt (Real.exp u) * ∫ t in Ioi (Real.exp u), f t| ≤ _
  rw [← integral_comp_exp_Ioi f u, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hv := mul_le_mul_of_nonneg_left (hi.trans_eq hvalue) (Real.sqrt_nonneg (Real.exp u))
  refine hv.trans_eq ?_
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
  unfold W
  calc
    _ = 16 * C * (1 + u / r)^2 *
        (Real.exp (u * (1 / 2)) * (Real.exp ((p - 3 / 4) * u) * Real.exp (-(1 / 4 : ℝ) * u))) := by
      ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

private theorem centered_sum_one_log (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, 0 ≤ u →
      |∑ n ∈ Finset.Icc 2 m,
        -(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u)| ≤
      K * ((m : ℝ) * (1 + Real.log m)) * Real.exp (-(orderRate m) * u) := by
  obtain ⟨Z, hZ, hspec⟩ := root_density_log_sq hRH
  let H := Z + 16 * ((Real.log 4 + 5) * 5000)
  have hH : 0 < H := by dsimp [H]; positivity
  have hTZ : 0 < trivialConstant := by unfold trivialConstant; positivity
  refine ⟨trivialConstant + 24 * H, by linarith, fun m hm u hu => ?_⟩
  let L := 1 + Real.log m
  let V := min ((1 + 2 * (u / (m + 1 : ℝ)))^2) (L^2)
  let W := Real.exp (-(orderRate m) * u)
  let w (n : ℕ) := Real.exp (-(u * ((m + 1 : ℝ)⁻¹ - (2 * (n : ℝ))⁻¹)))
  let S := Finset.Icc 2 m
  have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hL : 0 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hm₁]
  have hW : 0 ≤ W := Real.exp_nonneg _
  have hpoint (n : ℕ) (hn : n ∈ S) :
      |-(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u)| ≤
        trivialConstant * L * W + if m + 1 ≤ 2 * n then H * V * W * w n else 0 := by
    obtain ⟨hn₂, hnm⟩ := Finset.mem_Icc.mp hn
    have hn₂' : (2 : ℝ) ≤ n := by exact_mod_cast hn₂
    have hn₀ : (0 : ℝ) < n := by linarith
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hln₀ : 0 ≤ 1 + Real.log n := by linarith [Real.log_nonneg (show (1 : ℝ) ≤ n by linarith)]
    have hln : 1 + Real.log n ≤ L := by dsimp [L]; linarith [Real.log_le_log hn₀ hnm']
    have hcenter := root_centered_log_bound hn₂ (div_nonneg hu hn₀.le)
    rw [mul_div_cancel₀ _ hn₀.ne'] at hcenter
    have hrate : Real.exp (-u / 2) ≤ W := by
      apply Real.exp_le_exp.mpr
      dsimp [W, orderRate]
      nlinarith only [mul_nonneg hu (show 0 ≤ (m + 1 : ℝ)⁻¹ by positivity)]
    have hb : |centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u| ≤
        trivialConstant * L * W :=
      hcenter.trans (mul_le_mul (mul_le_mul_of_nonneg_left hln hTZ.le) hrate
        (Real.exp_nonneg _) (by positivity))
    have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := n)
    rw [abs_mul, abs_neg]
    refine (mul_le_of_le_one_left (abs_nonneg _) hμ).trans ?_
    unfold capturedSpectrum
    by_cases hsmall : 2 * n < m + 1
    · simpa only [ite_eq_left hsmall, ite_eq_right (not_le_of_gt hsmall), add_zero] using hb
    have hbig := le_of_not_gt hsmall
    rw [ite_eq_right hsmall, ite_eq_left hbig, sub_zero]
    have hexp : Real.exp (((2 * (n : ℝ))⁻¹ - 1 / 2) * u) = W * w n := by
      dsimp only [W, w, orderRate]
      rw [← Real.exp_add]
      congr 1
      ring
    have hboundSpectrum : |centered (n : ℝ) (Real.exp u)| ≤
        trivialConstant * L * W + H * L^2 * W * w n := by
      have ht := hspec n hn₂' u
      rw [hexp] at ht
      have hc : Z * (1 + Real.log n)^2 ≤ H * L^2 :=
        mul_le_mul (by dsimp [H]; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)])
          (pow_le_pow_left₀ hln₀ hln _) (sq_nonneg _) hH.le
      have hs := ht.trans (mul_le_mul_of_nonneg_right hc (mul_nonneg hW (Real.exp_nonneg _)))
      calc
        _ ≤ |centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u| + |rootDensity (n : ℝ) u| := by
          nth_rw 1 [← sub_add_cancel (centered (n : ℝ) (Real.exp u)) (rootDensity (n : ℝ) u)]
          exact abs_add_le _ _
        _ ≤ _ := add_le_add hb (hs.trans_eq (by ring))
    have hboundChebyshev : |centered (n : ℝ) (Real.exp u)| ≤
        trivialConstant * L * W + H * (1 + 2 * (u / (m + 1 : ℝ)))^2 * W * w n := by
      have ht := centered_chebyshev_log hRH hn₂' hu
      rw [hexp] at ht
      have hidx : (m + 1 : ℝ) / 2 ≤ n := by
        have hi : (m + 1 : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hbig
        linarith
      have hlog : u / (n : ℝ) ≤ 2 * (u / (m + 1 : ℝ)) :=
        (div_le_div_of_nonneg_left hu (by positivity) hidx).trans_eq (by
          field_simp)
      have hc : (16 * ((Real.log 4 + 5) * 5000)) * (1 + u / (n : ℝ))^2 ≤
          H * (1 + 2 * (u / (m + 1 : ℝ)))^2 :=
        mul_le_mul (by dsimp [H]; linarith)
          (pow_le_pow_left₀ (by positivity) (by linarith) _) (sq_nonneg _) hH.le
      have hs := ht.trans (mul_le_mul_of_nonneg_right hc (mul_nonneg hW (Real.exp_nonneg _)))
      exact (hs.trans_eq (by ring)).trans (le_add_of_nonneg_left (by positivity))
    by_cases h : (1 + 2 * (u / (m + 1 : ℝ)))^2 ≤ L^2
    · simpa only [V, min_eq_left h] using hboundChebyshev
    · simpa only [V, min_eq_right (le_of_not_ge h)] using hboundSpectrum
  have hcard : (S.card : ℝ) ≤ m := by
    exact_mod_cast (show S.card ≤ m by dsimp [S]; rw [Nat.card_Icc]; omega)
  have hgeom : V * (∑ n ∈ S.filter (fun n => m + 1 ≤ 2 * n), w n) ≤ 24 * (m : ℝ) * L :=
    omitted_root_weight_sum_le hm hu
  calc
    _ ≤ ∑ n ∈ S, |-(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ S, (trivialConstant * L * W + if m + 1 ≤ 2 * n then H * V * W * w n else 0) :=
      Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * (trivialConstant * L * W) + (H * W) *
        (V * ∑ n ∈ S.filter (fun n => m + 1 ≤ 2 * n), w n) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      congr 1
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ _ := by
      refine (add_le_add (mul_le_mul_of_nonneg_right hcard (by positivity))
        (mul_le_mul_of_nonneg_left hgeom (by positivity))).trans_eq ?_
      ring

private theorem all_orders_density_one_log (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, Real.log 2 ≤ u →
      |rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2)| ≤
        K * ((m : ℝ) * (1 + Real.log m)) * Real.exp (-(orderRate m) * u) := by
  obtain ⟨L, hL, hsum'⟩ := centered_sum_one_log hRH
  let A := (Real.log 4 + 4) * 4 * (1 + 2 / Real.log 2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 ≤ C := abs_nonneg _
  refine ⟨A + L + C, by linarith, fun m hm u hu => ?_⟩
  let x := Real.exp u
  let W := Real.exp (-(orderRate m) * u)
  let T (n : ℕ) := Real.sqrt x * (∫ t in Ioi x, psi (t ^ (n : ℝ)⁻¹) / t ^ 2)
  let e (n : ℕ) := -(μ n : ℝ) * (centered (n : ℝ) x - capturedSpectrum m n u)
  let R := Real.sqrt x * (primeTail x - Q x) - ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * T n
  let E := RHSharpActualEnvelope.G u - Real.exp (-u / 2) * (actualH u).re
  have hx : 2 ≤ x := by
    have hexp : Real.exp (Real.log 2) ≤ Real.exp u := Real.exp_le_exp.mpr hu
    simpa only [x, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hexp
  have hx0 : 0 < x := by linarith
  have hu0 : 0 ≤ u := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hu
  have hW : 0 < W := Real.exp_pos _
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hR : |R| ≤ A * (m : ℝ) * W := integrated_mobius_linear hm hx
  have hE : |E| ≤ C * W := by
    refine (abs_G_sub_normalized_actualH_le hu0).le.trans ?_
    dsimp only [W]
    rw [mul_comm (Real.exp _)]
    apply mul_le_mul (le_abs_self _) _ (Real.exp_nonneg _) hC
    apply Real.exp_le_exp.mpr
    unfold orderRate
    nlinarith [mul_nonneg (show 0 ≤ (m + 1 : ℝ)⁻¹ by positivity) hu0]
  let M := (1 + Real.log m)
  have hM : 1 ≤ M := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ m by linarith)
    dsimp [M]
    linarith
  have hsum : |∑ n ∈ Finset.Icc 2 m, e n| ≤ L * ((m : ℝ) * M) * W :=
    hsum' m hm u hu0
  have hterms (n : ℕ) (hn : n ∈ Finset.Icc 2 m) :
      (μ n : ℝ) * T n + retainedDensity m n u + e n = 0 := by
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have ht := root_tail_main (r := (n : ℝ)) hn1 hx0
    change T n = (n : ℝ) / ((n : ℝ) - 1) * x ^ ((n : ℝ)⁻¹ - 1 / 2) + centered (n : ℝ) x at ht
    have hpow : x ^ ((n : ℝ)⁻¹ - 1 / 2) = Real.exp (-(arithmeticRate n) * u) := by
      dsimp only [x, arithmeticRate]
      rw [← Real.exp_mul]
      congr 1
      ring
    rw [ht, hpow]
    unfold retainedDensity e
    ring
  have hs : (∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * T n) +
      (∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) +
      (∑ n ∈ Finset.Icc 2 m, e n) = 0 := by
    simp_rw [← Finset.sum_add_distrib]
    exact (Finset.sum_congr rfl hterms).trans Finset.sum_const_zero
  have hsplit : rootWindowDensity u - ∑ n ∈ Finset.Icc 2 m, retainedDensity m n u =
      -R + (∑ n ∈ Finset.Icc 2 m, e n) + E - 2 := by
    dsimp only [R, E, rootWindowDensity, x]
    linear_combination -hs
  rw [show rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2) =
      -R + (∑ n ∈ Finset.Icc 2 m, e n) + E by linarith only [hsplit]]
  have hm₁ : (1 : ℝ) ≤ m := by linarith
  have hms : (m : ℝ) ≤ (m : ℝ) * M := by
    simpa using mul_le_mul_of_nonneg_left hM (show 0 ≤ (m : ℝ) by positivity)
  have hms₁ : (1 : ℝ) ≤ (m : ℝ) * M := hm₁.trans hms
  calc
    _ ≤ |R| + |∑ n ∈ Finset.Icc 2 m, e n| + |E| := by
      calc
        _ ≤ |-R + ∑ n ∈ Finset.Icc 2 m, e n| + |E| := abs_add_le _ _
        _ ≤ (|-R| + |∑ n ∈ Finset.Icc 2 m, e n|) + |E| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ = _ := by rw [abs_neg]
    _ ≤ A * ((m : ℝ) * M) * W + L * ((m : ℝ) * M) * W + C * ((m : ℝ) * M) * W :=
      add_le_add (add_le_add (hR.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hms hA.le) hW.le)) hsum)
        (hE.trans (mul_le_mul_of_nonneg_right
          (by simpa using mul_le_mul_of_nonneg_left hms₁ hC) hW.le))
    _ = _ := by dsimp only [M]; ring

open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean
  (windowError normalizedMass normalizedZeroSeries)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
  (prime_window_remainder_of_rh spectralPrimitive windowDiscrepancy)

/-- Under RH, one pair of constants bounds the prime-window residual at every truncation degree. -/
theorem prime_window_mobius_one_log_of_rh (hRH : RiemannHypothesis) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a)) -
        (∑ n ∈ Finset.Icc 3 m, -(μ n : ℝ) *
          (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
          (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) -
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
        K * ((m : ℝ) * (1 + Real.log m)) *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2)) := by
  obtain ⟨K, hK, hD⟩ := all_orders_density_one_log hRH
  exact prime_window_of_density_bound hRH (fun m => (m : ℝ) * (1 + Real.log m))
    (fun m hm => by
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      exact mul_nonneg (Nat.cast_nonneg m) (by linarith only [Real.log_nonneg hm'])) retainedDensity
    (fun m n hn a B ha hB => by
      simpa only [arithmeticPrimitive, capturedPrimitive, powerGap, arithmeticRate, neg_sub]
        using retainedDensity_integral (m := m) hn ha hB)
    hK hD

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
