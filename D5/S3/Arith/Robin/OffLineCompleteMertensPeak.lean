/- GID: D5/S3/Arith/Robin/OffLineCompleteMertensPeak
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OffLineCompleteMertensPeak
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An off-line zero forces a finite complete Mertens peak and an actual Robin violator. -/

import D5.S3.Arith.Robin.FullZeroGaussianResponse
import D5.S3.Arith.Robin.CompleteMertensPeak
import D5.S3.Arith.Robin.GaussianPeakLocalization

/-! The integrated zero formula converts a localized Gaussian response into an arithmetic peak. -/

namespace D5.S3.Arith.Robin.OffLineCompleteMertensPeak

open MeasureTheory Set
open FullZeroGaussianResponse ZeroCoefficientBudget CompleteMertensPeak
open PrimeFiberPropagation

noncomputable section

private def correction (y : ℝ) : ℝ :=
  ∑' k : ℕ, Real.exp (-2 * (k + 1 : ℝ) * y) /
    (2 * (k + 1 : ℝ) * (2 * (k + 1 : ℝ) + 1))

private theorem correction_lt_half {y : ℝ} (hy : 0 < y) : correction y < 1 / 2 := by
  let q : ℕ → ℝ := fun k => (1 / 2) * (1 / (k + 1 : ℝ) - 1 / (k + 2 : ℝ))
  have hq0 (k : ℕ) : 0 ≤ q k := by
    dsimp [q]
    have h := one_div_le_one_div_of_le (by positivity : 0 < (k + 1 : ℝ))
      (by linarith : (k + 1 : ℝ) ≤ k + 2)
    linarith
  have hpartial (n : ℕ) : ∑ k ∈ Finset.range n, q k ≤ 1 / 2 := by
    have heq : ∑ k ∈ Finset.range n, q k = (1 / 2) * (1 - 1 / (n + 1 : ℝ)) := by
      simp only [q, ← Finset.mul_sum]
      have hh := Finset.sum_range_sub' (fun k : ℕ => 1 / (k + 1 : ℝ)) n
      simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add, one_div_one,
        add_assoc, one_add_one_eq_two] using congrArg (fun a : ℝ => (1 / 2) * a) hh
    rw [heq]
    have : 0 ≤ 1 / (n + 1 : ℝ) := by positivity
    linarith
  have hqs := summable_of_sum_range_le hq0 hpartial
  have hqsum := Real.tsum_le_of_sum_range_le hq0 hpartial
  let f : ℕ → ℝ := fun k => Real.exp (-2 * (k + 1 : ℝ) * y) /
    (2 * (k + 1 : ℝ) * (2 * (k + 1 : ℝ) + 1))
  have hlt (k : ℕ) : f k < q k := by
    have hk : 0 < (k + 1 : ℝ) := by positivity
    have hexp : Real.exp (-2 * (k + 1 : ℝ) * y) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith)
    have hden : 0 < 2 * (k + 1 : ℝ) * (2 * (k + 1 : ℝ) + 1) := by positivity
    calc
      f k < 1 / (2 * (k + 1 : ℝ) * (2 * (k + 1 : ℝ) + 1)) :=
        (div_lt_div_iff_of_pos_right hden).mpr hexp
      _ ≤ 1 / (2 * (k + 1 : ℝ) * (k + 2 : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)
      _ = q k := by dsimp [q]; field_simp; ring
  have hfs : Summable f := hqs.of_nonneg_of_le (fun k => by dsimp [f]; positivity)
    (fun k => (hlt k).le)
  exact (Summable.tsum_lt_tsum (fun k => (hlt k).le) (hlt 0) hfs hqs).trans_le hqsum

private theorem exponential_gap {β γ m : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1)
    (hγ : 10 < γ)
    (hm₀ : 100 * (γ + 10) ^ 2 * ((β - 1 / 2) ^ 2)⁻¹ ≤ m)
    (hm₁ : m ≤ 500 * (γ + 10) ^ 4 * ((β - 1 / 2) ^ 2)⁻¹) :
    2000 * m * (γ + 10) ^ 2 * Real.exp (33 * m / 4) <
      Real.exp ((β ^ 2 + 16 * β) * m) / 2 := by
  let δ := β - 1 / 2
  let D := γ + 10
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδh : δ < 1 / 2 := by dsimp [δ]; linarith
  have hD : 20 < D := by dsimp [D]; linarith
  have hD0 : 0 < D := by linarith
  have hd2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  change 100 * D ^ 2 * (δ ^ 2)⁻¹ ≤ m at hm₀
  change m ≤ 500 * D ^ 4 * (δ ^ 2)⁻¹ at hm₁
  have hm : 0 < m := (by positivity : 0 < 100 * D ^ 2 * (δ ^ 2)⁻¹).trans_le hm₀
  have hlogC : Real.log (2000000 : ℝ) < 20 := by
    have heq : Real.log (2000000 : ℝ) = 7 * Real.log 2 + 6 * Real.log 5 := by
      rw [show (2000000 : ℝ) = 2 ^ 7 * 5 ^ 6 by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
      norm_num
    rw [heq]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hlogD : Real.log D < D := by linarith [Real.log_le_sub_one_of_pos hD0]
  have hlogδ : Real.log δ⁻¹ < δ⁻¹ := by
    linarith [Real.log_le_sub_one_of_pos (inv_pos.mpr hδ)]
  have hlog : Real.log (4000 * m * D ^ 2) < 20 + 6 * D + 2 / δ := by
    have harg : 4000 * m * D ^ 2 ≤ 2000000 * D ^ 6 * (δ⁻¹) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right hm₁ (show 0 ≤ 4000 * D ^ 2 by positivity)
      convert hh using 1 <;> field_simp <;> ring
    have hmono := Real.log_le_log (by positivity : 0 < 4000 * m * D ^ 2) harg
    have heq : Real.log (2000000 * D ^ 6 * (δ⁻¹) ^ 2) =
        Real.log 2000000 + 6 * Real.log D + 2 * Real.log δ⁻¹ := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
      norm_num
    rw [heq] at hmono
    simp only [div_eq_mul_inv]
    linarith
  have hpay : 20 + 6 * D + 2 / δ < D ^ 2 / δ := by
    apply (lt_div_iff₀ hδ).mpr
    have hfirst : 20 * δ + 6 * D * δ + 2 < 3 * D + 12 := by
      nlinarith [mul_pos hD0 (sub_pos.mpr hδh)]
    have hsecond : 3 * D + 12 < D ^ 2 := by nlinarith
    have heq : (20 + 6 * D + 2 / δ) * δ = 20 * δ + 6 * D * δ + 2 := by
      field_simp
    rw [heq]
    exact hfirst.trans hsecond
  have hlarge : D ^ 2 / δ < 17 * δ * m := by
    have hlower : 100 * D ^ 2 ≤ m * δ ^ 2 := by
      exact (div_le_iff₀ hd2).mp (by simpa [div_eq_mul_inv] using hm₀)
    apply (div_lt_iff₀ hδ).mpr
    nlinarith [sq_pos_of_pos hD0]
  have hgap : (β ^ 2 + 16 * β) * m - 33 * m / 4 = (17 * δ + δ ^ 2) * m := by
    dsimp [δ]; ring
  have hexponent : Real.log (4000 * m * D ^ 2) <
      (β ^ 2 + 16 * β) * m - 33 * m / 4 := by
    rw [hgap]
    exact (hlog.trans hpay |>.trans hlarge).trans_le (by nlinarith [mul_nonneg hd2.le hm.le])
  have he := (Real.log_lt_iff_lt_exp (by positivity : 0 < 4000 * m * D ^ 2)).mp hexponent
  have hex := mul_lt_mul_of_pos_right he (Real.exp_pos (33 * m / 4))
  rw [← Real.exp_add] at hex
  rw [show (β ^ 2 + 16 * β) * m - 33 * m / 4 + 33 * m / 4 =
    (β ^ 2 + 16 * β) * m by ring] at hex
  change 2000 * m * D ^ 2 * Real.exp (33 * m / 4) < _
  linarith

/-- An off-line zero forces a complete Mertens peak in an explicit interval,
and hence an actual lcm integer strictly violating Robin's inequality. -/
theorem off_line_complete_mertens_peak {ι : Type*} [Countable ι] (ρ : ι → ℂ)
    (hstrip : ∀ i, 0 < (ρ i).re ∧ (ρ i).re < 1)
    (conjIndex : ι ≃ ι) (hconj : ∀ i, ρ (conjIndex i) = star (ρ i))
    (hlow : ∀ i, 10 < |(ρ i).im|)
    (hmass : HasSum (fun i => (ρ i * (1 - ρ i))⁻¹) (massConstant : ℂ))
    (hformula : ∀ y : ℝ, 0 < y → Hc ρ y =
      ((U (Real.exp y) - Real.log (2 * Real.pi) +
        ∑' k : ℕ, Real.exp (-2 * (k + 1 : ℝ) * y) /
          (2 * (k + 1 : ℝ) * (2 * (k + 1 : ℝ) + 1)) : ℝ) : ℂ))
    (i₀ : ι) (hβ : (1 / 2 : ℝ) < (ρ i₀).re) (hγ : 0 < (ρ i₀).im)
    (hJY : ∀ u : ℝ, 2 ≤ u → |Chebyshev.psi u - u| ≤
      (939 / 100) * u * (Real.log u) ^ (303 / 200 : ℝ) *
        Real.exp (-(4137 / 5000) * Real.sqrt (Real.log u)))
    (hLay : ∀ t : ℝ, 2 ≤ t → Q t = Chebyshev.psi t / t -
      (∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) +
        Real.log t - 1 - Real.eulerMascheroniConstant) :
    let δ := (ρ i₀).re - 1 / 2
    let D := (ρ i₀).im + 10
    let m₀ := 100 * D ^ 2 * (δ ^ 2)⁻¹
    let m₁ := 500 * D ^ 4 * (δ ^ 2)⁻¹
    let B₀ := Real.exp (4 * (28 * m₁ + 20) ^ 2)
    ∃ A ∈ Set.Icc (Real.exp (4 * m₀)) (Real.exp (28 * m₁)),
      Real.sqrt A * (4 * Real.log A + 9) < U A ∧
      ∃ t ∈ Set.Icc A (Real.exp (4 * (Real.log A + 20) ^ 2)),
        Set.Icc A (Real.exp (4 * (Real.log A + 20) ^ 2)) ⊆ Set.Icc A B₀ ∧
        let N := Nat.lcmUpto ⌊t⌋₊
        5040 < N ∧ (N : ℝ) ≤ Real.exp (B₀ * Real.log B₀) ∧
          divisorRatio N > Real.exp Real.eulerMascheroniConstant * Real.log (Real.log N) := by
  let δ := (ρ i₀).re - 1 / 2
  let D := (ρ i₀).im + 10
  let m₀ := 100 * D ^ 2 * (δ ^ 2)⁻¹
  let m₁ := 500 * D ^ 4 * (δ ^ 2)⁻¹
  let B₀ := Real.exp (4 * (28 * m₁ + 20) ^ 2)
  change ∃ A ∈ Set.Icc (Real.exp (4 * m₀)) (Real.exp (28 * m₁)),
    Real.sqrt A * (4 * Real.log A + 9) < U A ∧
    ∃ t ∈ Set.Icc A (Real.exp (4 * (Real.log A + 20) ^ 2)),
      Set.Icc A (Real.exp (4 * (Real.log A + 20) ^ 2)) ⊆ Set.Icc A B₀ ∧
      let N := Nat.lcmUpto ⌊t⌋₊
      5040 < N ∧ (N : ℝ) ≤ Real.exp (B₀ * Real.log B₀) ∧
        divisorRatio N > Real.exp Real.eulerMascheroniConstant * Real.log (Real.log N)
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδh : δ < 1 / 2 := by dsimp [δ]; linarith [(hstrip i₀).2]
  have hγ10 : 10 < (ρ i₀).im := by simpa only [abs_of_pos hγ] using hlow i₀
  have hD : 20 < D := by dsimp [D]; linarith
  have hd2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hm₀large : 160000 < m₀ := by
    dsimp only [m₀]
    rw [← div_eq_mul_inv, lt_div_iff₀ hd2]
    nlinarith [mul_pos (by linarith : 0 < δ + 1 / 2) (sub_pos.mpr hδh),
      sq_nonneg (D - 20)]
  obtain ⟨m, hm₀, hm₁, hm, _, _, hiK, hiV, hK, hmain, hsmall, _, hkernel⟩ :=
    full_zero_gaussian_response ρ hstrip conjIndex hconj hlow hmass i₀ hβ hγ
  change m₀ ≤ m at hm₀
  change m ≤ m₁ at hm₁
  obtain ⟨_, _, _, _, _, _, hH, _⟩ :=
    zero_coefficient_budget ρ hstrip conjIndex hconj hlow hmass
  have hex : ∃ y ∈ Set.Icc (4 * m) (28 * m),
      (4 * y + 11) * Real.exp (y / 2) < H ρ y := by
    by_contra hnone
    have hnopeak : ∀ y ∈ Set.Icc (4 * m) (28 * m),
        H ρ y ≤ (4 * y + 11) * Real.exp (y / 2) := by
      intro y hy
      exact not_lt.mp (fun hh => hnone ⟨y, hy, hh⟩)
    have hup := GaussianPeakLocalization.gaussian_peak_localization (H ρ) hm hγ10
      hiK hiV (fun y => (hH y).2.2) hsmall hkernel hnopeak
    have hgap := exponential_gap hβ (hstrip i₀).2 hγ10 hm₀ hm₁
    rw [hK] at hup
    linarith
  obtain ⟨y, hy, hypeak⟩ := hex
  have hy0 : 0 < y := by linarith [hy.1, hm₀]
  have hHU : H ρ y ≤ U (Real.exp y) := by
    have hreal := congrArg Complex.re (hformula y hy0)
    change H ρ y = U (Real.exp y) - Real.log (2 * Real.pi) + correction y at hreal
    have hR := correction_lt_half hy0
    have hlogpi : 1 < Real.log (2 * Real.pi) :=
      (Real.lt_log_iff_exp_lt (by positivity)).mpr
        (Real.exp_one_lt_three.trans (by linarith [Real.pi_gt_three]))
    linarith
  let A := Real.exp y
  have hA0 : 0 < A := Real.exp_pos _
  have hlogA : Real.log A = y := Real.log_exp _
  have hA : 10000 ≤ A := by
    have he := Real.add_one_le_exp y
    dsimp [A]
    linarith [hy.1, hm₀]
  have hAinterval : A ∈ Set.Icc (Real.exp (4 * m₀)) (Real.exp (28 * m₁)) := by
    constructor <;> apply Real.exp_le_exp.mpr
    · linarith [hy.1]
    · linarith [hy.2]
  have hsqrt : Real.sqrt A = Real.exp (y / 2) := by
    dsimp [A]
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  have hpeak : Real.sqrt A * (4 * Real.log A + 9) < U A := by
    rw [hlogA, hsqrt]
    have he := Real.exp_pos (y / 2)
    dsimp only [A]
    nlinarith
  have hstrong : Real.sqrt A * (4 * Real.log A ^ 2 / (1 + Real.log A) + 9) < U A := by
    have hden : 0 < 1 + Real.log A := by rw [hlogA]; linarith
    have hlinear : 4 * Real.log A ^ 2 / (1 + Real.log A) < 4 * Real.log A := by
      apply (div_lt_iff₀ hden).mpr
      rw [hlogA]
      nlinarith
    have hs := Real.sqrt_pos.mpr hA0
    nlinarith
  obtain ⟨t, ht, hN, hNbound, hRobin⟩ := complete_mertens_peak hJY hLay hA hstrong
  let B := Real.exp (4 * (Real.log A + 20) ^ 2)
  have hBB₀ : B ≤ B₀ := by
    apply Real.exp_le_exp.mpr
    have hupper : Real.log A ≤ 28 * m₁ := by rw [hlogA]; linarith [hy.2]
    have hlower : 0 ≤ Real.log A := by rw [hlogA]; exact hy0.le
    nlinarith
  have hB0 : 0 < B := Real.exp_pos _
  have hlogB : 0 ≤ Real.log B := by dsimp [B]; rw [Real.log_exp]; positivity
  have hproduct : B * Real.log B ≤ B₀ * Real.log B₀ :=
    mul_le_mul hBB₀ (Real.log_le_log hB0 hBB₀) hlogB (hB0.le.trans hBB₀)
  refine ⟨A, hAinterval, hpeak, t, ht, ?_, hN, ?_, hRobin⟩
  · intro x hx
    exact ⟨hx.1, hx.2.trans hBB₀⟩
  · exact hNbound.trans (Real.exp_le_exp.mpr hproduct)

end

end D5.S3.Arith.Robin.OffLineCompleteMertensPeak
