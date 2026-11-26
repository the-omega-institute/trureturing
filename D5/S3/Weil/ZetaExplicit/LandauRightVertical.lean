/- GID: D5/S3/Weil/ZetaExplicit/LandauRightVertical
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaExplicit/LandauRightVertical
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The right vertical integral of the finite Landau contour has a uniform bound. -/

import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Dirichlet

namespace D5.S3.Weil.ZetaExplicit.LandauRightVertical

open Complex Finset MeasureTheory
open scoped ArithmeticFunction

private noncomputable def landauCoeff (x c : ℝ) (n : ℕ) : ℝ :=
  x ^ c * (Λ n / (n : ℝ) ^ c)

private noncomputable def landauTerm (x c : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (landauCoeff x c n : ℂ) * Complex.exp
    ((((Real.log x - Real.log (n : ℝ) : ℝ) : ℂ) * I) * t)

private lemma landauCoeff_nonneg {x c : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ landauCoeff x c n :=
  mul_nonneg (Real.rpow_nonneg hx _) (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg n.cast_nonneg _))

private lemma landauTerm_norm {x c : ℝ} (hx : 0 ≤ x) (n : ℕ) (t : ℝ) :
    ‖landauTerm x c n t‖ = landauCoeff x c n := by
  have hphase (g : ℝ) : ‖Complex.exp (((g : ℂ) * I) * t)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [landauTerm, norm_mul, hphase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (landauCoeff_nonneg hx n)]

private lemma coeff_summable (x : ℝ) {c : ℝ} (hc : 1 < c) :
    Summable (landauCoeff x c) := by
  apply Summable.mul_left
  have h : LSeriesSummable (fun n => (Λ n : ℂ)) (c : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc)
  refine (summable_norm_iff.mpr h).congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · simp [hn, Complex.norm_real,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

private lemma term_eq {x c : ℝ} (hx : 0 < x) (n : ℕ) (t : ℝ) :
    (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) *
        LSeries.term (fun n => (Λ n : ℂ)) ((c : ℂ) + (t : ℂ) * I) n =
      landauTerm x c n t := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero, landauTerm, landauCoeff]
  · have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    let s : ℂ := (c : ℂ) + (t : ℂ) * I
    change (x : ℂ) ^ s * LSeries.term (fun n => (Λ n : ℂ)) s n = _
    rw [LSeries.term_of_ne_zero hn, mul_div_assoc', mul_comm ((x : ℂ) ^ s),
      mul_div_assoc, ← Complex.ofReal_natCast,
      ← Complex.div_cpow_ofReal_nonneg hx.le hn0.le, ← Complex.ofReal_div]
    have hratio : 0 < x / (n : ℝ) := div_pos hx hn0
    change (Λ n : ℂ) * ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) = _
    rw [cpow_add _ _ (Complex.ofReal_ne_zero.mpr hratio.ne'), ← Complex.ofReal_cpow hratio.le,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hratio.ne'),
      ← Complex.ofReal_log hratio.le, Real.log_div hx.ne' hn0.ne', Real.div_rpow hx.le hn0.le]
    unfold landauTerm landauCoeff
    push_cast
    ring_nf

private lemma integralExpansion {x c : ℝ} (hx : 0 < x) (hc : 1 < c) (V : ℝ) :
    HasSum (fun n : ℕ => ∫ t in 1..V, landauTerm x c n t)
      (∫ t in 1..V, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) *
        (- deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) / riemannZeta ((c : ℂ) + (t : ℂ) * I))) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n (_ : ℝ) => landauCoeff x c n) ?_ ?_ ?_ intervalIntegrable_const ?_
  · intro n
    exact (show Continuous (landauTerm x c n) by unfold landauTerm; fun_prop).aestronglyMeasurable
  · intro n
    exact ae_of_all _ fun t _ => (landauTerm_norm hx.le n t).le
  · exact ae_of_all _ fun _ _ => coeff_summable x hc
  · refine ae_of_all _ fun t _ => ?_
    let s : ℂ := (c : ℂ) + (t : ℂ) * I
    have hs : 1 < s.re := by simpa [s] using hc
    change HasSum (fun n : ℕ => landauTerm x c n t)
      ((x : ℂ) ^ s * (- deriv riemannZeta s / riemannZeta s))
    rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
    have h := ((ArithmeticFunction.LSeriesSummable_vonMangoldt hs).hasSum).mul_left ((x : ℂ) ^ s)
    exact h.congr_fun fun n => (term_eq (c := c) hx n t).symm

private lemma phaseNorm (g t : ℝ) : ‖Complex.exp (((g : ℂ) * I) * t)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

private lemma oscillatoryBound {g V : ℝ} (hg : g ≠ 0) :
    ‖∫ t in 1..V, Complex.exp (((g : ℂ) * I) * t)‖ ≤ 2 / |g| := by
  have hmode : (g : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hg) I_ne_zero
  rw [integral_exp_mul_complex hmode, norm_div, norm_mul, norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg g)
  exact (norm_sub_le _ _).trans (by rw [phaseNorm, phaseNorm]; norm_num)

private lemma intervalLengthBound {g V : ℝ} (hV : 1 ≤ V) :
    ‖∫ t in 1..V, Complex.exp (((g : ℂ) * I) * t)‖ ≤ V - 1 := by
  simpa [abs_of_nonneg (sub_nonneg.mpr hV)] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 1) (b := V) (C := 1) fun t _ => (phaseNorm g t).le)

private lemma logGap {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |x - y| / max x y ≤ |Real.log x - Real.log y| := by
  have ordered {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
      (b - a) / b ≤ Real.log b - Real.log a := by
    have hb := ha.trans_le hab
    simpa [Real.log_div hb.ne' ha.ne', inv_div, sub_div, div_self hb.ne'] using
      Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
  rcases le_total x y with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h), neg_sub,
      abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hx h)), neg_sub]
    exact ordered hx h
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h),
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy h))]
    exact ordered hy h

/-- Integrating a dominating power bounds the real Dirichlet coefficients as the line
approaches the pole.  The indices zero and one are absent. -/
private lemma farSeries {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, Λ (n + 2) / ((n + 2 : ℕ) : ℝ) ^ s) ≤ 4 / (s - 1)^2 := by
  let a := (s - 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hexp : a - s < -1 := by dsimp [a]; linarith
  have hp : ∀ n : ℕ, 0 < ((n + 2 : ℕ) : ℝ) := fun n => by positivity
  have hanti : AntitoneOn (fun x : ℝ => x ^ (a - s)) (Set.Ici 1) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) hxy (by linarith)
  have hint := integrableOn_Ioi_rpow_of_lt hexp zero_lt_one
  have hnonneg : ∀ t : ℝ, t ∈ Set.Ioi 1 → 0 ≤ t ^ (a - s) := fun t ht => by
    exact Real.rpow_nonneg (zero_le_one.trans (le_of_lt ht)) _
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (a - s)) 1
    (by simpa only [Nat.cast_one] using hanti)
    (by simpa only [Nat.cast_one] using hint)
    (by simpa only [Nat.cast_one] using hnonneg)
  simp only [Nat.cast_one] at htail
  rw [integral_Ioi_rpow_of_lt hexp zero_lt_one, Real.one_rpow] at htail
  have hbase : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (a - s)) := by
    exact (summable_nat_add_iff 2).2 (Real.summable_nat_rpow.mpr hexp)
  have hterm (n : ℕ) :
      Λ (n + 2) / ((n + 2 : ℕ) : ℝ) ^ s ≤ (((n + 2 : ℕ) : ℝ) ^ (a - s)) / a := by
    have hlog := (ArithmeticFunction.vonMangoldt_le_log (n := n + 2)).trans
      (Real.log_le_rpow_div (le_of_lt (hp n)) ha)
    calc
      _ ≤ ((((n + 2 : ℕ) : ℝ) ^ a) / a) / ((n + 2 : ℕ) : ℝ) ^ s :=
        div_le_div_of_nonneg_right hlog (Real.rpow_nonneg (hp n).le _)
      _ = _ := by rw [Real.rpow_sub (hp n)]; ring
  have hscaled := hbase.div_const a
  have hsLambda := Summable.of_nonneg_of_le
    (fun n : ℕ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (hp n).le _))
    hterm hscaled
  calc
    _ ≤ ∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ (a - s)) / a := hsLambda.tsum_le_tsum hterm hscaled
    _ = (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (a - s)) / a := tsum_div_const
    _ ≤ (-(1 / (a - s + 1))) / a := by
      exact div_le_div_of_nonneg_right (by simpa [Nat.add_assoc, neg_div, one_div] using htail) ha.le
    _ = _ := by
      have hden : a - s + 1 = -a := by dsimp [a]; ring
      have htwo : s - 1 = 2 * a := by dsimp [a]; ring
      rw [hden, htwo]
      field_simp [ne_of_gt ha]
      norm_num

/-- Excluding one nearest integer, the two sides are bounded by shifted harmonic sums. -/
private lemma reciprocalSum {x : ℝ} {k N : ℕ} {s : Finset ℕ} (hk : k ≤ N)
    (hs : ∀ n ∈ s, n ≤ N ∧ n ≠ k) (hx : |x - (k : ℝ)| ≤ 1 / 2) :
    (∑ n ∈ s, |x - (n : ℝ)|⁻¹) ≤ 4 * (1 + Real.log (N : ℝ)) := by
  have recipBound {n d : ℕ} (hd : 0 < d)
      (habs : |(n : ℝ) - (k : ℝ)| = (d : ℝ)) :
      |x - (n : ℝ)|⁻¹ ≤ 2 * (d : ℝ)⁻¹ := by
    have hsum := abs_sub_le (n : ℝ) x (k : ℝ)
    rw [habs, abs_sub_comm (n : ℝ) x] at hsum
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hdist : (d : ℝ) / 2 ≤ |x - (n : ℝ)| := by linarith
    have hpos : 0 < (d : ℝ) := by exact_mod_cast hd
    exact (inv_anti₀ (half_pos hpos) hdist).trans_eq (by ring)
  have hside (t : Finset ℕ) (d : ℕ → ℕ)
      (hdi : ∀ n ∈ t, d n ∈ Finset.Icc 1 N) (hinj : Set.InjOn d (↑t : Set ℕ))
      (hb : ∀ n ∈ t, |x - (n : ℝ)|⁻¹ ≤ 2 * (d n : ℝ)⁻¹) :
      (∑ n ∈ t, |x - (n : ℝ)|⁻¹) ≤ 2 * (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ n ∈ t, 2 * (d n : ℝ)⁻¹ := sum_le_sum hb
      _ = ∑ n ∈ t.image d, 2 * (n : ℝ)⁻¹ := (sum_image (f := fun n : ℕ => 2 * (n : ℝ)⁻¹) hinj).symm
      _ ≤ ∑ n ∈ Finset.Icc 1 N, 2 * (n : ℝ)⁻¹ := by
        apply sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun j _ _ => by positivity)
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hj
        exact hdi n hn
      _ = _ := by rw [← mul_sum, harmonic_eq_sum_Icc]; push_cast; rfl
  have hl : (∑ n ∈ s.filter (· < k), |x - (n : ℝ)|⁻¹) ≤ 2 * (harmonic N : ℝ) := by
    refine hside _ (fun n => k - n) (fun n hn => ?_) (fun n hn m hm hnm => ?_)
      (fun n hn => ?_)
    · have hnk := (mem_filter.mp hn).2
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · have hnk := (mem_filter.mp hn).2
      have hmk := (mem_filter.mp hm).2
      change k - n = k - m at hnm
      omega
    · have hnk := (mem_filter.mp hn).2
      apply recipBound (show 0 < k - n by omega)
      have hle : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnk.le
      rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub, Nat.cast_sub hnk.le]
  have hr : (∑ n ∈ s.filter (fun n => ¬ n < k), |x - (n : ℝ)|⁻¹) ≤
      2 * (harmonic N : ℝ) := by
    have above {n : ℕ} (hn : n ∈ s.filter (fun n => ¬ n < k)) : k < n := by
      have h := mem_filter.mp hn
      have hne := (hs n h.1).2
      omega
    refine hside _ (fun n => n - k) (fun n hn => ?_) (fun n hn m hm hnm => ?_)
      (fun n hn => ?_)
    · have hkn := above hn
      have hN := (hs n (mem_filter.mp hn).1).1
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · have hn' := above hn
      have hm' := above hm
      change n - k = m - k at hnm
      omega
    · have hkn := above hn
      apply recipBound (show 0 < n - k by omega)
      have hle : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn.le
      rw [abs_of_nonneg (sub_nonneg.mpr hle), Nat.cast_sub hkn.le]
  rw [← sum_filter_add_sum_filter_not s (· < k)]
  linarith [harmonic_le_one_add_log N]

open Real in
private lemma movingLineBounds {x : ℝ} (hx : 1 < x) :
    let c := 1 + (Real.log (3 * x))⁻¹
    1 < c ∧ c ≤ 2 ∧ x ^ c ≤ 3 * x ∧ 1 / 2 ≤ Real.log (2 * x) ∧ Real.log (3 * x) ≤ 2 * Real.log (2 * x) := by
  have hx0 : 0 < x := by linarith
  have h₁ : 1 < Real.log (3 * x) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact Real.exp_one_lt_three.trans (by linarith)
  have h₂ : 1 / 2 ≤ Real.log (2 * x) :=
    (show (1 / 2 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]).trans
      (log_le_log (by norm_num) (by linarith))
  have hlog : Real.log x ≤ Real.log (3 * x) := log_le_log hx0 (by linarith)
  have h₃ : x ^ (Real.log (3 * x))⁻¹ ≤ 3 := by
    rw [rpow_def_of_pos hx0]
    have hm : Real.log x * (Real.log (3 * x))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by linarith : 0 < Real.log (3 * x))]
      exact hlog
    exact (exp_le_exp.mpr hm).trans exp_one_lt_three.le
  dsimp
  refine ⟨lt_add_of_pos_right _ (inv_pos.mpr (by linarith)), ?_, ?_, h₂, ?_⟩
  · linarith [inv_le_one_of_one_le₀ h₁.le]
  · rw [rpow_add hx0, rpow_one]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left h₃ hx0.le
  · calc
      _ ≤ Real.log ((2 * x) ^ 2) := log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num

private lemma nearestBounds {x : ℝ} (hx : 1 < x) :
    let k := (round x).toNat
    |x - (k : ℝ)| ≤ 1 / 2 ∧ x / 2 ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * x := by
  have hd := abs_sub_round x
  have h := abs_le.mp hd
  have hk : 0 ≤ round x := by
    have hk : (0 : ℝ) ≤ (round x : ℝ) := by linarith [h.2]
    exact_mod_cast hk
  have he : ((round x).toNat : ℝ) = (round x : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
  dsimp
  rw [he]
  exact ⟨hd, by linarith [h.2], by linarith [h.1]⟩

/-- A uniform right-edge estimate for the finite Landau rectangle.  The choice of
line depends on the base, and the nearest integer term is allowed to resonate. -/
theorem norm_right_vertical_integral {x V : ℝ} (hx : 1 < x) (hV : 1 < V) :
    let c := 1 + (Real.log (3 * x))⁻¹
    ‖∫ t in 1..V, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) *
      (- deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) / riemannZeta ((c : ℂ) + (t : ℂ) * I))‖ ≤
        let logHeight := Real.log
        400 * (V * logHeight (2 * x) + x * (logHeight (2 * x))^2) := by
  let c := 1 + (Real.log (3 * x))⁻¹
  let k := (round x).toNat
  let N := ⌊2 * x⌋₊
  let L := Real.log (2 * x)
  let nearby := ((Finset.Icc 2 N).filter (fun n : ℕ => x / 2 ≤ (n : ℝ))).erase k
  let area (n : ℕ) := ∫ t in 1..V, landauTerm x c n t
  have hx0 : 0 < x := by linarith
  have h2x : 0 ≤ 2 * x := by positivity
  obtain ⟨hc, hc2, hxc, hL, hL3⟩ := movingLineBounds hx
  obtain ⟨hround, hklo, hkhi⟩ := nearestBounds hx
  have hkN : k ≤ N := (Nat.le_floor_iff h2x).mpr hkhi
  have hN : 2 ≤ N := (Nat.le_floor_iff h2x).mpr (by push_cast; linarith)
  have hNlog : Real.log (N : ℝ) ≤ L :=
    Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) (Nat.floor_le h2x)
  have expansion := integralExpansion hx0 hc V
  have hnSummable := expansion.summable.norm
  have coeffNear {n : ℕ} (hn : 2 ≤ n) (hlo : x / 2 ≤ (n : ℝ)) (hhi : (n : ℝ) ≤ 2 * x) :
      landauCoeff x c n ≤ 4 * L := by
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hr₀ := (div_pos hx0 hn0).le
    have hr₂ : x / (n : ℝ) ≤ 2 := (div_le_iff₀ hn0).mpr (by linarith)
    have hp : (x / (n : ℝ)) ^ c ≤ 4 := by
      calc
        _ ≤ (2 : ℝ) ^ c := Real.rpow_le_rpow hr₀ hr₂ (by linarith)
        _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc2
        _ = 4 := by norm_num [Real.rpow_two]
    have hl := ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 hhi)
    calc
      landauCoeff x c n = Λ n * (x / (n : ℝ)) ^ c := by
        simp [landauCoeff, Real.div_rpow hx0.le hn0.le]
        ring
      _ ≤ L * 4 := mul_le_mul hl hp (Real.rpow_nonneg hr₀ _) (by linarith)
      _ = _ := by ring
  have areaNorm (n : ℕ) :
      ‖area n‖ = landauCoeff x c n *
        ‖∫ t in 1..V, Complex.exp ((((Real.log x - Real.log (n : ℝ) : ℝ) : ℂ) * I) * t)‖ := by
    dsimp only [area, landauTerm]
    rw [intervalIntegral.integral_const_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (landauCoeff_nonneg hx0.le n)]
  let b₁ (n : ℕ) := if n = k then 4 * V * L else 0
  let b₂ (n : ℕ) := if n ∈ nearby then 16 * x * L * |x - (n : ℝ)|⁻¹ else 0
  let b₃ (n : ℕ) := 4 * landauCoeff x c n
  have h₁ : ∀ n, 0 ≤ b₁ n := fun n => by dsimp [b₁]; split <;> positivity
  have h₂ : ∀ n, 0 ≤ b₂ n := fun n => by dsimp [b₂]; split <;> positivity
  have h₃ : ∀ n, 0 ≤ b₃ n := fun n => mul_nonneg (by norm_num) (landauCoeff_nonneg hx0.le n)
  -- The nearest integer uses the interval length.  The comparable and far terms
  -- use the oscillatory bound at their respective logarithmic gaps.
  have hPoint (n : ℕ) : ‖area n‖ ≤ (b₁ n + b₂ n) + b₃ n := by
    by_cases hn : 2 ≤ n
    · have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      by_cases hnk : n = k
      · subst n
        have ha := intervalLengthBound (g := Real.log x - Real.log (k : ℝ)) hV.le
        have hCoeff := coeffNear hn hklo hkhi
        have hBound : ‖area k‖ ≤ b₁ k := by
          rw [areaNorm]
          dsimp [b₁]
          rw [ite_eq_left rfl]
          calc
            _ ≤ (4 * L) * (V - 1) := mul_le_mul hCoeff ha (norm_nonneg _) (by positivity)
            _ ≤ 4 * V * L := by nlinarith
        linarith [h₂ k, h₃ k]
      by_cases hnear : n ∈ nearby
      · have hnNear := Finset.mem_filter.mp (Finset.mem_erase.mp hnear).2
        have hhi := (Nat.le_floor_iff h2x).mp (Finset.mem_Icc.mp hnNear.1).2
        have hCoeff := coeffNear hn hnNear.2 hhi
        have hdist : 0 < |x - (n : ℝ)| := by
          apply abs_pos.mpr
          intro he
          have hlow : 1 ≤ |(n : ℝ) - (k : ℝ)| := by
            rcases lt_or_gt_of_ne hnk with h | h
            · have hr : (n : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (show n + 1 ≤ k by omega)
              rw [abs_of_nonpos (by linarith)]
              linarith
            · have hr : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (show k + 1 ≤ n by omega)
              rw [abs_of_nonneg (by linarith)]
              linarith
          have hEq : x = (n : ℝ) := sub_eq_zero.mp he
          have hrounded : |(n : ℝ) - (k : ℝ)| ≤ 1 / 2 :=
            (congrArg (fun z : ℝ => |z - (k : ℝ)|) hEq.symm).le.trans hround
          linarith
        have hgap : |x - (n : ℝ)| / (2 * x) ≤ |Real.log x - Real.log (n : ℝ)| := by
          refine (div_le_div_of_nonneg_left (abs_nonneg _) (hx0.trans_le (le_max_left _ _))
            (max_le (by linarith) hhi)).trans (logGap hx0 hn0)
        have hgpos := (div_pos hdist (by positivity : 0 < 2*x)).trans_le hgap
        have hg : Real.log x - Real.log (n : ℝ) ≠ 0 := abs_pos.mp hgpos
        have hphase := oscillatoryBound (V := V) hg
        have hBound : ‖area n‖ ≤ b₂ n := by
          rw [areaNorm]
          simp only [b₂, ite_eq_left hnear]
          calc
            _ ≤ (4 * L) * (2 / |Real.log x - Real.log (n : ℝ)|) :=
              mul_le_mul hCoeff hphase (norm_nonneg _) (by positivity)
            _ ≤ (4 * L) * (2 / (|x - (n : ℝ)| / (2 * x))) := by
              gcongr
            _ = _ := by field_simp [hx0.ne', hdist.ne']; ring
        linarith [h₁ n, h₃ n]
      have hfar : (n : ℝ) < x / 2 ∨ 2 * x < (n : ℝ) := by
        by_contra! h
        exact hnear (Finset.mem_erase.mpr ⟨hnk, Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hn, (Nat.le_floor_iff h2x).mpr h.2⟩, h.1⟩⟩)
      have hgap : (1 / 2 : ℝ) ≤ |Real.log x - Real.log (n : ℝ)| := by
        refine le_trans ?_ (logGap hx0 hn0)
        rcases hfar with h | h
        · rw [max_eq_left (by linarith), abs_of_nonneg (by linarith)]
          exact (le_div_iff₀ hx0).mpr (by linarith)
        · rw [max_eq_right (by linarith), abs_of_nonpos (by linarith), neg_sub]
          exact (le_div_iff₀ hn0).mpr (by linarith)
      have hg : Real.log x - Real.log (n : ℝ) ≠ 0 := by
        intro he
        norm_num [he] at hgap
      have hPhase4 := (oscillatoryBound (V := V) hg).trans
        ((div_le_iff₀ (abs_pos.mpr hg)).mpr (by linarith : 2 ≤ 4 * |Real.log x - Real.log (n : ℝ)|))
      have hBound : ‖area n‖ ≤ b₃ n := by
        rw [areaNorm]
        dsimp only [b₃]
        rw [mul_comm 4]
        exact mul_le_mul_of_nonneg_left hPhase4 (landauCoeff_nonneg hx0.le n)
      linarith [h₁ n, h₂ n]
    have hz : landauCoeff x c n = 0 := by
      interval_cases n <;> simp [landauCoeff, ArithmeticFunction.vonMangoldt_apply_one]
    rw [areaNorm, hz, zero_mul]
    linarith [h₁ n, h₂ n, h₃ n]
  have hb₁ (n : ℕ) (hn : n ∉ ({k} : Finset ℕ)) : b₁ n = 0 := by
    exact ite_eq_right (fun h => hn (Finset.mem_singleton.mpr h))
  have hb₂ (n : ℕ) (hn : n ∉ nearby) : b₂ n = 0 := ite_eq_right hn
  have sum₁ : Summable b₁ := summable_of_ne_finset_zero hb₁
  have sum₂ : Summable b₂ := summable_of_ne_finset_zero hb₂
  have sum₃ := (coeff_summable x hc).mul_left 4
  have eval₁ : ∑' n, b₁ n = 4 * V * L := by
    rw [tsum_eq_sum hb₁, Finset.sum_singleton]
    exact ite_eq_left rfl
  have eval₂ : (∑' n, b₂ n) ≤ 192 * x * L^2 := by
    have hs (n : ℕ) (hn : n ∈ nearby) : n ≤ N ∧ n ≠ k := by
      have he := Finset.mem_erase.mp hn
      exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp he.2).1).2, he.1⟩
    rw [tsum_eq_sum hb₂]
    calc
      _ = (16 * x * L) * ∑ n ∈ nearby, |x - (n : ℝ)|⁻¹ := by
        rw [Finset.mul_sum]
        exact sum_congr rfl (fun n hn => ite_eq_left hn)
      _ ≤ (16 * x * L) * (4 * (1 + Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_left (reciprocalSum hkN hs hround) (by positivity)
      _ ≤ _ := by
        have hl3 : 1 + Real.log (N : ℝ) ≤ 3 * L := by linarith
        exact (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hl3 (by norm_num : (0:ℝ) ≤ 4))
          (by positivity : 0 ≤ 16 * x * L)).trans_eq (by ring)
  have eval₃ : (∑' n, b₃ n) ≤ 192 * x * L^2 := by
    have hshift := (coeff_summable x hc).sum_add_tsum_nat_add 2
    have hlow : ∑ n ∈ Finset.range 2, landauCoeff x c n = 0 := by
      norm_num [Finset.sum_range_succ, landauCoeff, ArithmeticFunction.vonMangoldt_apply_one]
    rw [hlow, zero_add] at hshift
    have hdelta : (c - 1)⁻¹ = Real.log (3 * x) := by
      dsimp [c]
      rw [add_comm, add_sub_cancel_right, inv_inv]
    have hseries : (∑' n : ℕ, Λ (n + 2) / ((n + 2 : ℕ) : ℝ) ^ c) ≤
        4 * (Real.log (3 * x)) ^ 2 := by
      calc
        _ ≤ 4 / (c - 1)^2 := farSeries hc
        _ = _ := by rw [div_eq_mul_inv, ← inv_pow, hdelta]
    calc
      _ = 4 * (x ^ c * ∑' n : ℕ, Λ (n + 2) / ((n + 2 : ℕ) : ℝ) ^ c) := by
        change (∑' n, 4 * landauCoeff x c n) = _
        rw [tsum_mul_left, ← hshift]
        simp only [landauCoeff, tsum_mul_left]
        rfl
      _ ≤ 4 * (3 * x * (4 * (2 * L)^2)) := by
        have hlog0 : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
        have hbig := hseries.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hlog0 hL3 2) (by norm_num : (0 : ℝ) ≤ 4))
        refine mul_le_mul_of_nonneg_left (mul_le_mul hxc hbig ?_ (by positivity))
          (by norm_num)
        exact tsum_nonneg (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.rpow_nonneg (by positivity) _))
      _ = _ := by ring
  change ‖_‖ ≤ 400 * (V * L + x * L^2)
  rw [← expansion.tsum_eq]
  calc
    _ ≤ ∑' n, ‖area n‖ := norm_tsum_le_tsum_norm hnSummable
    _ ≤ ∑' n, ((b₁ n + b₂ n) + b₃ n) := hnSummable.tsum_le_tsum hPoint ((sum₁.add sum₂).add sum₃)
    _ = ((∑' n, b₁ n) + (∑' n, b₂ n)) + (∑' n, b₃ n) := by
      rw [Summable.tsum_add (sum₁.add sum₂) sum₃, Summable.tsum_add sum₁ sum₂]
    _ ≤ _ := by rw [eval₁]; nlinarith [show 0 ≤ x * L^2 by positivity]

end D5.S3.Weil.ZetaExplicit.LandauRightVertical
