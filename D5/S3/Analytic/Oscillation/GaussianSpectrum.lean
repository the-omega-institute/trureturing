/- GID: D5/S3/Analytic/Oscillation/GaussianSpectrum
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/GaussianSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Counting estimates control Gaussian spectral mass and continuous cosine sums. -/

import D5.S3.Analytic.Oscillation.OrdinateCounting
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Gaussian weights on a locally finite positive spectrum. -/

namespace D5.S3.Analytic.Oscillation.GaussianSpectrum

open D5.S3.Analytic.Oscillation.OrdinateCounting
open Set Filter
open scoped Topology BigOperators

noncomputable section

lemma spectrum_countable (S : Spectrum) : Countable S.index := by
  apply Set.countable_univ_iff.mp
  have h := Set.countable_iUnion (fun n : ℕ => (S.finite_le (n : ℝ)).countable)
  apply h.mono
  intro j _
  obtain ⟨n, hn⟩ := exists_nat_ge (S.gamma j)
  exact Set.mem_iUnion.mpr ⟨n, hn⟩

def LocalCount (S : Spectrum) : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧ ∀ t : ℝ, 0 ≤ t →
    (S.N (t + 1) : ℝ) - (S.N t : ℝ) ≤ A * Real.log (t + 3)

noncomputable def gaussianMass (S : Spectrum) (M : ℝ) : ℝ :=
  ∑' j : S.index, (S.mult j : ℝ) * Real.exp (-S.gamma j ^ 2 / (2 * M ^ 2))

noncomputable def gaussianCos (S : Spectrum) (M y : ℝ) : ℝ :=
  ∑' j : S.index, (S.mult j : ℝ) * Real.exp (-S.gamma j ^ 2 / (2 * M ^ 2)) *
    Real.cos (S.gamma j * y)

/-- The asymptotic count gives a uniform logarithmic counting bound. -/
theorem count_bound (S : Spectrum) (hN : CountAsymptotic S) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (S.N T : ℝ) ≤ C * T * Real.log (2 + T) := by
  let c : ℝ := 1 / (2 * Real.pi) + 1
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨A, hA⟩ := eventually_atTop.1
    (hN.eventually (gt_mem_nhds (show 1 / (2 * Real.pi) < c by dsimp [c]; linarith)))
  let L := max A 4
  let B : ℝ := S.N L
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨c + B / Real.log 3, by positivity, ?_⟩
  intro T hT
  have hT0 : 0 < T := by linarith
  have hlog : Real.log 3 ≤ Real.log (2 + T) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogpos : 0 < Real.log (2 + T) := hlog3.trans_le hlog
  by_cases hLT : L ≤ T
  · have hT4 : 4 ≤ T := (le_max_right A 4).trans hLT
    have hh := (div_lt_iff₀ (mul_pos hT0 (Real.log_pos (by linarith)))).mp
      (hA T ((le_max_left A 4).trans hLT))
    have hl := Real.log_le_log hT0 (show T ≤ 2 + T by linarith)
    have hb : 0 ≤ B / Real.log 3 * T * Real.log (2 + T) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hl (mul_nonneg hc.le hT0.le)]
  · have hh : (S.N T : ℝ) ≤ B := count_mono S (le_of_not_ge hLT)
    have hb : B ≤ B / Real.log 3 * Real.log (2 + T) := by
      calc
        B = B / Real.log 3 * Real.log 3 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
    have hb' := le_mul_of_one_le_left (by positivity : 0 ≤ B / Real.log 3 *
      Real.log (2 + T)) hT
    have hp : 0 ≤ c * T * Real.log (2 + T) := by positivity
    nlinarith

/-- Multiplicity-weighted inverse squares are summable. -/
theorem inverse_square_summable (S : Spectrum) (hN : CountAsymptotic S) :
    Summable (fun j : S.index => (S.mult j : ℝ) / S.gamma j ^ 2) := by
  obtain ⟨C, hC, htail⟩ := inverse_square_tail S hN
  apply (S.finite_le 4).summable_compl_iff.mp
  have heq : {j | S.gamma j ≤ 4}ᶜ = {j | 4 < S.gamma j} := by ext j; simp
  rw [heq]
  exact (htail 4 (by norm_num)).1

private lemma exp_weight_le {M g : ℝ} (hM : 0 < M) (hg : 0 < g) :
    Real.exp (-g ^ 2 / (2 * M ^ 2)) ≤ (2 * M ^ 2) / g ^ 2 := by
  have hx : 0 < g ^ 2 / (2 * M ^ 2) := by positivity
  have he : g ^ 2 / (2 * M ^ 2) ≤ Real.exp (g ^ 2 / (2 * M ^ 2)) :=
    le_trans (by linarith) (Real.add_one_le_exp _)
  rw [neg_div, Real.exp_neg]
  calc
    (Real.exp (g ^ 2 / (2 * M ^ 2)))⁻¹ ≤ (g ^ 2 / (2 * M ^ 2))⁻¹ :=
      inv_anti₀ hx he
    _ = _ := by rw [inv_div]

/-- Gaussian spectral coefficients are summable at every positive scale. -/
theorem gaussian_coefficients_summable (S : Spectrum) (hN : CountAsymptotic S)
    {M : ℝ} (hM : 0 < M) :
    Summable (fun j : S.index =>
      (S.mult j : ℝ) * Real.exp (-S.gamma j ^ 2 / (2 * M ^ 2))) := by
  apply ((inverse_square_summable S hN).mul_left (2 * M ^ 2)).of_nonneg_of_le
  · intro j; positivity
  · intro j
    calc
      _ ≤ (S.mult j : ℝ) * ((2 * M ^ 2) / S.gamma j ^ 2) :=
        mul_le_mul_of_nonneg_left (exp_weight_le hM (S.gamma_pos j)) (Nat.cast_nonneg _)
      _ = _ := by ring

private lemma cosine_term_norm_le (S : Spectrum) (M y : ℝ) (j : S.index) :
    ‖(S.mult j : ℝ) * Real.exp (-S.gamma j ^ 2 / (2 * M ^ 2)) *
      Real.cos (S.gamma j * y)‖ ≤
      (S.mult j : ℝ) * Real.exp (-S.gamma j ^ 2 / (2 * M ^ 2)) := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity)
    (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (S.gamma j * y))

/-- Gaussian cosine coefficients are absolutely summable. -/
theorem gaussianCos_summable (S : Spectrum) (hN : CountAsymptotic S)
    {M : ℝ} (hM : 0 < M) (y : ℝ) :
    Summable (fun j : S.index =>
      (S.mult j : ℝ) * Real.exp (-S.gamma j ^ 2 / (2 * M ^ 2)) *
        Real.cos (S.gamma j * y)) := by
  exact Summable.of_norm_bounded (gaussian_coefficients_summable S hN hM)
    (cosine_term_norm_le S M y)

/-- The Gaussian cosine sum is continuous in its spatial argument. -/
theorem gaussianCos_continuous (S : Spectrum) (hN : CountAsymptotic S)
    {M : ℝ} (hM : 0 < M) : Continuous (gaussianCos S M) := by
  exact continuous_tsum
    (fun j => continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    (gaussian_coefficients_summable S hN hM) (fun j y => cosine_term_norm_le S M y j)

/-- The total Gaussian mass uniformly bounds the cosine sum. -/
theorem abs_gaussianCos_le (S : Spectrum) (hN : CountAsymptotic S)
    {M : ℝ} (hM : 0 < M) (y : ℝ) :
    |gaussianCos S M y| ≤ gaussianMass S M := by
  exact (norm_tsum_le_tsum_norm (gaussianCos_summable S hN hM y).norm).trans
    ((gaussianCos_summable S hN hM y).norm.tsum_le_tsum
      (cosine_term_norm_le S M y) (gaussian_coefficients_summable S hN hM))

/-- The Gaussian mass has order at most M log(2+M). -/
theorem gaussian_mass_bound (S : Spectrum) (hN : CountAsymptotic S) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M →
      gaussianMass S M ≤ C * M * Real.log (2 + M) := by
  classical
  obtain ⟨B, hB, hcount⟩ := count_bound S hN
  obtain ⟨K, hK, htail⟩ := inverse_square_tail S hN
  refine ⟨8 * B + K + 1, by positivity, ?_⟩
  intro M hM
  have hM0 : 0 < M := by linarith
  have hcoef := gaussian_coefficients_summable S hN hM0
  have ht := htail (4 * M) (by linarith)
  have heq : (fun j => j ∉ S.cut (4 * M)) = (fun j => 4 * M < S.gamma j) := by
    funext j
    simp [Spectrum.cut]
  have ht' : Summable (fun j : {j : S.index // j ∉ S.cut (4 * M)} =>
      (S.mult j.val : ℝ) / S.gamma j.val ^ 2) := by
    rw [heq]
    exact ht.1
  have htbound : (∑' j : {j : S.index // j ∉ S.cut (4 * M)},
      (S.mult j.val : ℝ) / S.gamma j.val ^ 2) ≤ K * Real.log (4 * M) / (4 * M) := by
    rw [heq]
    exact ht.2
  have hlow : (∑ j ∈ S.cut (4 * M),
      (S.mult j : ℝ) * Real.exp (-S.gamma j ^ 2 / (2 * M ^ 2))) ≤
      (S.N (4 * M) : ℝ) := by
    rw [Spectrum.N, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_of_le_one_right (Nat.cast_nonneg _)
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  have hhigh : (∑' j : {j : S.index // j ∉ S.cut (4 * M)},
      (S.mult j.val : ℝ) * Real.exp (-S.gamma j.val ^ 2 / (2 * M ^ 2))) ≤
      2 * M ^ 2 * (K * Real.log (4 * M) / (4 * M)) := by
    calc
      _ ≤ ∑' j : {j : S.index // j ∉ S.cut (4 * M)},
          (2 * M ^ 2) * ((S.mult j.val : ℝ) / S.gamma j.val ^ 2) := by
        apply (hcoef.subtype _).tsum_le_tsum _ (ht'.mul_left _)
        intro j
        calc
          _ ≤ (S.mult j.val : ℝ) * ((2 * M ^ 2) / S.gamma j.val ^ 2) :=
            mul_le_mul_of_nonneg_left (exp_weight_le hM0 (S.gamma_pos _))
              (Nat.cast_nonneg _)
          _ = _ := by ring
      _ = (2 * M ^ 2) * ∑' j : {j : S.index // j ∉ S.cut (4 * M)},
          (S.mult j.val : ℝ) / S.gamma j.val ^ 2 := by rw [tsum_mul_left]
      _ ≤ _ := mul_le_mul_of_nonneg_left htbound (by positivity)
  have hlog : Real.log (2 + 4 * M) ≤ 2 * Real.log (2 + M) := by
    calc
      _ ≤ Real.log ((2 + M) ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith [sq_nonneg M])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlog' : Real.log (4 * M) ≤ 2 * Real.log (2 + M) :=
    (Real.log_le_log (by positivity) (by linarith : 4 * M ≤ 2 + 4 * M)).trans hlog
  have hlo := (hcount (4 * M) (by linarith)).trans
    (mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ B * (4 * M)))
  have hhi : 2 * M ^ 2 * (K * Real.log (4 * M) / (4 * M)) =
      K * M / 2 * Real.log (4 * M) := by field_simp; ring
  have hh := mul_le_mul_of_nonneg_left hlog' (by positivity : 0 ≤ K * M / 2)
  have hlogpos : 0 < Real.log (2 + M) := Real.log_pos (by linarith)
  unfold gaussianMass
  rw [← hcoef.sum_add_tsum_subtype_compl (S.cut (4 * M))]
  rw [hhi] at hhigh
  nlinarith

/-- Unit-window counts control every transition band of width between one and M. -/
theorem transition_mass_bound (S : Spectrum) (hlocal : LocalCount S) :
    ∃ C : ℝ, 0 < C ∧ ∀ M Δ : ℝ,
      1 ≤ M → 1 ≤ Δ → Δ ≤ M →
      (S.N (M + Δ) : ℝ) - (S.N M : ℝ) ≤ C * Δ * Real.log (2 + M) := by
  obtain ⟨A, hA, hlocal⟩ := hlocal
  refine ⟨4 * A, by linarith, ?_⟩
  intro M Δ hM hΔ hΔM
  let n : ℕ := ⌈Δ⌉₊
  have hnlo : Δ ≤ (n : ℝ) := Nat.le_ceil Δ
  have hnhi : (n : ℝ) < Δ + 1 := Nat.ceil_lt_add_one (by linarith)
  have hlogpos : 0 ≤ Real.log (2 + M) := (Real.log_pos (by linarith)).le
  have hstep (k : ℕ) (hk : k ∈ Finset.range n) :
      (S.N (M + (k + 1 : ℕ)) : ℝ) - (S.N (M + k) : ℝ) ≤
        2 * A * Real.log (2 + M) := by
    have hk' : (k : ℝ) < n := by exact_mod_cast Finset.mem_range.mp hk
    have hlocal' := hlocal (M + k) (by positivity)
    have hlog : Real.log (M + k + 3) ≤ 2 * Real.log (2 + M) := by
      calc
        _ ≤ Real.log ((2 + M) ^ 2) :=
          Real.log_le_log (by positivity) (by nlinarith [sq_nonneg M])
        _ = _ := by rw [Real.log_pow]; norm_num
    have hh := hlocal'.trans (mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ A))
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, mul_left_comm, mul_assoc] using hh
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_range_sub (fun k : ℕ => (S.N (M + k) : ℝ)),
    Nat.cast_zero, add_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hmono := count_mono S (show M + Δ ≤ M + n by linarith)
  have hprod := mul_le_mul_of_nonneg_right (show (n : ℝ) ≤ 2 * Δ by linarith)
    (show 0 ≤ 2 * A * Real.log (2 + M) by positivity)
  nlinarith

end
end D5.S3.Analytic.Oscillation.GaussianSpectrum
