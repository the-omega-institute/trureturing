import D5.S3.Weil.Mertens.IntegratedExplicit.FiniteSpectralOscillation
import D5.S3.Weil.Mertens.IntegratedExplicit.GaussianLeadingSpectrum
import D5.S3.Weil.Mertens.IntegratedExplicit.TriangularPolePreservation

/-! The dominant Gaussian modes are an actual finite real exponential sum,
with uniform signed excursions and exponentially decaying remaining modes. -/

noncomputable section

open Set
open scoped ComplexConjugate

namespace ActualGaussianLeadingOscillation

open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualData actual_height_gt_ten)
open GaussianLeadingSpectrum FiniteSpectralOscillation TriangularPolePreservation

def mode (v : ℝ) (n : ℕ) : ℂ := exponent v (actualData.zero n)
def frequency (v : ℝ) (n : ℕ) : ℝ := (mode v n).im
def normalized (v topScore T : ℝ) : ℂ :=
  ∑' n : ℕ, distinctCoeff n * Complex.exp ((T : ℂ) * (mode v n - (topScore : ℂ)))

private theorem mode_conjugate (v : ℝ) (n : ℕ) :
    mode v (actualData.conjugation n) = conj (mode v n) := by
  rw [mode, actualData.zero_conjugation]
  simp only [mode, exponent, map_add, map_div₀, map_mul, map_pow,
    Complex.conj_ofReal, map_ofNat]

private theorem frequency_ne_zero {v : ℝ} (hv : 0 ≤ v) (n : ℕ) : frequency v n ≠ 0 := by
  let z := actualData.zero n
  have hheight := actual_height_gt_ten z (actualData.zero_isNontrivial n)
  have hi : z.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at hheight
    norm_num at hheight
  have hz : 0 < z.re := (actualData.zero_isNontrivial n).2.1
  have hfreq : frequency v n = z.im * (1 + v * z.re) := by
    unfold frequency mode exponent
    change (z + (v : ℂ) * z ^ 2 / 2).im = _
    rw [div_eq_mul_inv, show ((2 : ℂ)⁻¹) = ((1 / 2 : ℝ) : ℂ) by norm_num, pow_two]
    simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, zero_mul, zero_add]
    ring
  rw [hfreq]
  exact mul_ne_zero hi (by nlinarith [mul_nonneg hv hz.le])

private theorem real_part_reconstruction {z : ℂ} :
    (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem dominant_modes {v topScore gap : ℝ} (hv : 0 ≤ v) (hgap : 0 < gap)
    (s : Finset ℕ) (hs : ∀ n, n ∈ s ↔ (mode v n).re = topScore)
    (htail : ∀ n ∉ s, (mode v n).re ≤ topScore - gap) (hne : s.Nonempty) :
    ∃ L κ : ℝ, 0 < L ∧ 0 < κ ∧
      (∀ a : ℝ, (∃ t ∈ Icc a (a + L), (series s distinctCoeff (frequency v) t).re < -κ) ∧
        (∃ t ∈ Icc a (a + L), κ < (series s distinctCoeff (frequency v) t).re)) ∧
      ∀ T ≥ 0, ‖normalized v topScore T - series s distinctCoeff (frequency v) T‖ ≤
        (∑' n : ℕ, ‖distinctCoeff n‖) * Real.exp (-gap * T) := by
  have hperm (n : ℕ) : actualData.conjugation n ∈ s ↔ n ∈ s := by
    rw [hs, hs, mode_conjugate, Complex.conj_re]
  have hinj : Set.InjOn (frequency v) (↑s : Set ℕ) := by
    intro i hi j hj h
    have hre := ((hs i).mp hi).trans ((hs j).mp hj).symm
    have hz := exponent_injective_on_right hv
      (show (actualData.zero i).re > 0 from (actualData.zero_isNontrivial i).2.1)
      (show (actualData.zero j).re > 0 from (actualData.zero_isNontrivial j).2.1)
      (Complex.ext hre h)
    exact actualData.zero_injective hz
  have hconj (n : ℕ) (t : ℝ) :
      distinctCoeff (actualData.conjugation n) * wave (frequency v (actualData.conjugation n)) t =
        conj (distinctCoeff n * wave (frequency v n) t) := by
    rw [distinctCoeff_conjugate]
    have hf : frequency v (actualData.conjugation n) = -frequency v n := by
      unfold frequency
      rw [mode_conjugate, Complex.conj_im]
    simp only [hf, wave, map_mul, ← Complex.exp_conj, Complex.conj_I,
      Complex.conj_ofReal, Complex.ofReal_neg, neg_mul, mul_neg]
  have hreal (t : ℝ) : (series s distinctCoeff (frequency v) t).im = 0 := by
    have eq : conj (series s distinctCoeff (frequency v) t) =
        series s distinctCoeff (frequency v) t := by
      unfold series
      rw [map_sum]
      simp_rw [← hconj _ t]
      apply Finset.sum_bij (fun i _ => actualData.conjugation i)
      · intro i hi
        exact (hperm i).mpr hi
      · intro i _ j _ h
        exact actualData.conjugation.injective h
      · intro j hj
        exact ⟨actualData.conjugation j, (hperm j).mpr hj,
          actualData.conjugation_conjugation j⟩
      · intro i _
        rfl
    have h := congrArg Complex.im eq
    rw [Complex.conj_im] at h
    linarith
  obtain ⟨i, hi⟩ := hne
  obtain ⟨L, hL, hexc⟩ := signed_excursions s distinctCoeff (frequency v)
    (fun n _ => frequency_ne_zero hv n) hinj hreal hi (distinctCoeff_ne_zero i)
  refine ⟨L, ‖distinctCoeff i‖ / 4, hL, by
    exact div_pos (norm_pos_iff.mpr (distinctCoeff_ne_zero i)) (by norm_num), hexc, ?_⟩
  intro T hT
  let F (n : ℕ) := distinctCoeff n * Complex.exp ((T : ℂ) * (mode v n - (topScore : ℂ)))
  have hnorm (n : ℕ) :
      ‖F n‖ = ‖distinctCoeff n‖ * Real.exp (T * ((mode v n).re - topScore)) := by
    simp only [F, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, zero_mul, sub_zero]
  have hall (n : ℕ) : (mode v n).re ≤ topScore := by
    by_cases hh : n ∈ s
    · exact ((hs n).mp hh).le
    · exact (htail n hh).trans (by linarith)
  have hn : Summable (fun n => ‖F n‖) := distinctCoeff_summable.of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => by
      rw [hnorm]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hT (sub_nonpos.mpr (hall n)))))
  have hmain : ∑ n ∈ s, F n = series s distinctCoeff (frequency v) T := by
    apply Finset.sum_congr rfl
    intro n hn'
    unfold F wave frequency
    congr 2
    have hmode : mode v n - (topScore : ℂ) = Complex.I * ((mode v n).im : ℂ) := by
      calc
        _ = ((mode v n).re : ℂ) + Complex.I * ((mode v n).im : ℂ) - (topScore : ℂ) := by
          rw [real_part_reconstruction]
        _ = _ := by rw [(hs n).mp hn']; ring
    rw [hmode]
    ring
  change ‖(∑' n, F n) - series s distinctCoeff (frequency v) T‖ ≤ _
  rw [← hn.of_norm.sum_add_tsum_subtype_compl s, hmain, add_sub_cancel_left]
  apply (norm_tsum_le_tsum_norm (hn.subtype _)).trans
  have hbd : Summable (fun n : ℕ => ‖distinctCoeff n‖ * Real.exp (-gap * T)) :=
    distinctCoeff_summable.mul_right _
  calc
    _ ≤ ∑' n : {j // j ∉ s}, ‖distinctCoeff n‖ * Real.exp (-gap * T) := by
      apply (hn.subtype _).tsum_le_tsum _ (hbd.subtype _)
      intro n
      change ‖F (n : ℕ)‖ ≤ ‖distinctCoeff (n : ℕ)‖ * Real.exp (-gap * T)
      rw [hnorm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (htail n n.property) hT
      linarith
    _ ≤ ∑' n : ℕ, ‖distinctCoeff n‖ * Real.exp (-gap * T) :=
      Summable.tsum_subtype_le (fun n => ‖distinctCoeff n‖ * Real.exp (-gap * T))
        {n : ℕ | n ∉ s} (fun _ => by positivity) hbd
    _ = _ := distinctCoeff_summable.tsum_mul_right _

end ActualGaussianLeadingOscillation

#print axioms ActualGaussianLeadingOscillation.dominant_modes
