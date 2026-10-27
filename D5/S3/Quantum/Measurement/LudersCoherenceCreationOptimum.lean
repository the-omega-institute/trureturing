/- GID: D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/LudersCoherenceCreationOptimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: General qubit measurements attain half the sum of coherence and Bloch length. -/

import D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation
import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation

/-! The optimal coherence of a qubit under arbitrary finite nonselective measurements. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation (l1Coherence)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
  (bloch norm_bloch_le_trace_of_posSemidef)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)

namespace D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum

/-- The nonselective measurement with the positive square roots of its effects. -/
def luders {n : ℕ} (e : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i, CFC.sqrt (e i) * ρ * CFC.sqrt (e i)

/-- The length of the Bloch vector in the computational basis. -/
def blochNorm (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Real.sqrt ((ρ 0 0 - ρ 1 1).re ^ 2 + 4 * ‖ρ 0 1‖ ^ 2)

private theorem hermitian_entries (m : Matrix (Fin 2) (Fin 2) ℂ) (hm : m.IsHermitian) :
    (m 0 0).im = 0 ∧ (m 1 1).im = 0 ∧ m 1 0 = star (m 0 1) := by
  have hzero (i : Fin 2) : (m i i).im = 0 := by
    have h := congrArg Complex.im (hm.apply i i)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  exact ⟨hzero 0, hzero 1, (hm.apply 1 0).symm⟩

private theorem coherence_two (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : ρ.IsHermitian) :
    l1Coherence ρ = 2 * ‖ρ 0 1‖ := by
  unfold l1Coherence
  simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, zero_add, add_zero,
    Fin.zero_ne_one, (by decide : (1 : Fin 2) ≠ 0),
    (hermitian_entries ρ hρ).2.2, norm_star]
  ring

private theorem luders_decomposition {n : ℕ} (ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (hρ : IsDensity ρ) (e : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (he : IsPOVM e) :
    ∃ (k : Fin n → ℝ) (z : Fin n → ℂ) (v : Fin n → ℝ),
      (∀ i, 0 ≤ k i) ∧ (∑ i, (k i + 2 * (‖z i‖ ^ 2 + v i ^ 2))) = 1 ∧
      (luders e ρ).IsHermitian ∧
      (luders e ρ) 0 1 = ∑ i, ((k i : ℂ) * ρ 0 1 +
        ((2 * (star (z i) * ρ 0 1).re + v i * (ρ 0 0 - ρ 1 1).re : ℝ) : ℂ) * z i) := by
  let m := fun i => CFC.sqrt (e i)
  have hm (i : Fin n) : (m i).PosSemidef := (CFC.sqrt_nonneg (e i)).posSemidef
  have hsum : ∑ i, m i * m i = 1 := by
    calc
      _ = ∑ i, e i := Finset.sum_congr rfl (fun i _ =>
        CFC.sqrt_mul_sqrt_self (e i) (he.1 i).nonneg)
      _ = 1 := he.2
  let p := fun i => (m i 0 0).re
  let q := fun i => (m i 1 1).re
  let z := fun i => m i 0 1
  let v := fun i => (p i - q i) / 2
  let k := fun i => p i * q i - ‖z i‖ ^ 2
  have h00 (i : Fin n) : m i 0 0 = (p i : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (hermitian_entries (m i) (hm i).isHermitian).1
  have h11 (i : Fin n) : m i 1 1 = (q i : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (hermitian_entries (m i) (hm i).isHermitian).2.1
  have h10 (i : Fin n) : m i 1 0 = star (z i) :=
    (hermitian_entries (m i) (hm i).isHermitian).2.2
  have hzsq (i : Fin n) : ‖z i‖ ^ 2 = (z i).re ^ 2 + (z i).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hk (i : Fin n) : 0 ≤ k i := by
    have hd := (Complex.nonneg_iff.mp (hm i).det_nonneg).1
    rw [Matrix.det_fin_two, h00 i, h11 i, h10 i] at hd
    change 0 ≤ ((p i : ℂ) * (q i : ℂ) - z i * star (z i)).re at hd
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, zero_mul, sub_zero] at hd
    dsimp only [k]
    nlinarith only [hd, hzsq i]
  have ht : ∑ i, (p i ^ 2 + q i ^ 2 + 2 * ‖z i‖ ^ 2) = 2 := by
    calc
      _ = ((∑ i, m i * m i) 0 0).re + ((∑ i, m i * m i) 1 1).re := by
        simp only [Matrix.sum_apply, Complex.re_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [hzsq i]
        simp only [Matrix.mul_apply, Fin.sum_univ_two, h00 i, h11 i, h10 i]
        change _ = (((p i : ℂ) * (p i : ℂ) + z i * star (z i)).re +
          (star (z i) * z i + (q i : ℂ) * (q i : ℂ)).re)
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.star_def, Complex.conj_re, Complex.conj_im]
        ring
      _ = 2 := by rw [hsum]; norm_num
  have hs : (∑ i, (k i + 2 * (‖z i‖ ^ 2 + v i ^ 2))) = 1 := by
    have halg (i : Fin n) : k i + 2 * (‖z i‖ ^ 2 + v i ^ 2) =
        (p i ^ 2 + q i ^ 2 + 2 * ‖z i‖ ^ 2) / 2 := by dsimp only [k, v]; ring
    simp_rw [halg]
    rw [← Finset.sum_div, ht]
    norm_num
  have hcancel : ∑ i, (((p i + q i) / 2 : ℝ) : ℂ) * z i = 0 := by
    have hi (i : Fin n) : (((p i + q i) / 2 : ℝ) : ℂ) * z i =
        (m i * m i) 0 1 / 2 := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two, h00 i, h11 i]
      change (((p i + q i) / 2 : ℝ) : ℂ) * z i =
        ((p i : ℂ) * z i + z i * (q i : ℂ)) / 2
      push_cast
      ring
    simp_rw [hi]
    rw [← Finset.sum_div, ← Matrix.sum_apply, hsum]
    norm_num
  have hr := hermitian_entries ρ hρ.1.isHermitian
  have hx : (ρ 0 0).re + (ρ 1 1).re = 1 := by
    have h := congrArg Complex.re hρ.2
    rw [Matrix.trace_fin_two, Complex.add_re] at h
    exact h
  have hf (i : Fin n) : (m i * ρ * m i) 0 1 = (k i : ℂ) * ρ 0 1 +
      ((2 * (star (z i) * ρ 0 1).re + v i * (ρ 0 0 - ρ 1 1).re : ℝ) : ℂ) * z i +
      (((p i + q i) / 2 : ℝ) : ℂ) * z i := by
    apply Complex.ext <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, h00 i, h11 i, hr.2.2]
    · dsimp only [k, v]
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
        Complex.conj_im, zero_mul, mul_zero, sub_zero, zero_add, hr.1, hr.2.1]
      rw [hzsq i]
      dsimp only [z]
      linear_combination (p i + q i) * (m i 0 1).re / 2 * hx
    · dsimp only [k, v]
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.mul_im, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
        Complex.conj_im, zero_mul, mul_zero, sub_zero, zero_add, hr.1, hr.2.1]
      rw [hzsq i]
      dsimp only [z]
      linear_combination (p i + q i) * (m i 0 1).im / 2 * hx
  refine ⟨k, z, v, hk, hs, ?_, ?_⟩
  · unfold luders
    change (∑ i, m i * ρ * m i).IsHermitian
    change (∑ i, m i * ρ * m i)ᴴ = _
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
      (hm _).isHermitian.eq, hρ.1.isHermitian.eq, Matrix.mul_assoc]
  · unfold luders
    change (∑ i, m i * ρ * m i) 0 1 = _
    simp only [Matrix.sum_apply, hf, Finset.sum_add_distrib, hcancel, add_zero]

private theorem quadratic_bound (s r t v : ℝ) (hs : 0 ≤ s) :
    s * t ^ 2 + |r| * t * v ≤
      ((s + Real.sqrt (r ^ 2 + s ^ 2)) / 2) * (t ^ 2 + v ^ 2) := by
  let d := Real.sqrt (r ^ 2 + s ^ 2)
  let l := (s + d) / 2
  have hd : d ^ 2 = r ^ 2 + s ^ 2 := Real.sq_sqrt (by positivity)
  have hds : s ≤ d := by
    have hn : 0 ≤ d := Real.sqrt_nonneg _
    nlinarith only [hd, hn, hs, sq_nonneg r]
  have hl : 0 ≤ l := by dsimp only [l]; linarith
  have hls : 0 ≤ l - s := by dsimp only [l]; linarith
  have hdisc : 4 * l * (l - s) = r ^ 2 := by dsimp only [l]; nlinarith only [hd]
  have ha := Real.sq_sqrt hls
  have hb := Real.sq_sqrt hl
  have hp : 2 * Real.sqrt (l - s) * Real.sqrt l = |r| := by
    have he : (2 * Real.sqrt (l - s) * Real.sqrt l) ^ 2 = |r| ^ 2 := by
      rw [mul_pow, mul_pow, ha, hb, sq_abs]
      nlinarith only [hdisc]
    have hn : 0 ≤ 2 * Real.sqrt (l - s) * Real.sqrt l := by positivity
    nlinarith only [he, hn, abs_nonneg r]
  have hid : (Real.sqrt (l - s) * t - Real.sqrt l * v) ^ 2 =
      (l - s) * t ^ 2 + l * v ^ 2 - |r| * t * v := by
    calc
      _ = Real.sqrt (l - s) ^ 2 * t ^ 2 + Real.sqrt l ^ 2 * v ^ 2 -
        (2 * Real.sqrt (l - s) * Real.sqrt l) * t * v := by ring
      _ = _ := by rw [ha, hb, hp]
  change _ ≤ l * (t ^ 2 + v ^ 2)
  nlinarith only [hid, sq_nonneg (Real.sqrt (l - s) * t - Real.sqrt l * v)]

private theorem dephasing_bound (c z : ℂ) (v r : ℝ) :
    2 * ‖((2 * (star z * c).re + v * r : ℝ) : ℂ) * z‖ ≤
      (‖z‖ ^ 2 + v ^ 2) * (2 * ‖c‖ + Real.sqrt (r ^ 2 + 4 * ‖c‖ ^ 2)) := by
  have he : |(star z * c).re| ≤ ‖z‖ * ‖c‖ := by
    simpa only [norm_mul, norm_star] using Complex.abs_re_le_norm (star z * c)
  have hr : |2 * (star z * c).re + v * r| ≤ 2 * ‖z‖ * ‖c‖ + |v| * |r| := by
    calc
      _ ≤ |2 * (star z * c).re| + |v * r| := abs_add_le _ _
      _ = 2 * |(star z * c).re| + |v| * |r| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ _ := by linarith
  have hq := quadratic_bound (2 * ‖c‖) r ‖z‖ |v| (by positivity)
  have hrad : r ^ 2 + (2 * ‖c‖) ^ 2 = r ^ 2 + 4 * ‖c‖ ^ 2 := by ring
  rw [hrad, sq_abs] at hq
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hm := mul_le_mul_of_nonneg_right hr (norm_nonneg z)
  nlinarith only [hm, hq]

private theorem radius_data (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ) :
    0 ≤ l1Coherence ρ ∧ l1Coherence ρ ≤ blochNorm ρ ∧ blochNorm ρ ≤ 1 ∧
      blochNorm ρ ^ 2 = (ρ 0 0 - ρ 1 1).re ^ 2 + l1Coherence ρ ^ 2 := by
  have hs := coherence_two ρ hρ.1.isHermitian
  have hsq : blochNorm ρ ^ 2 = (ρ 0 0 - ρ 1 1).re ^ 2 + l1Coherence ρ ^ 2 := by
    rw [hs]
    unfold blochNorm
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hn : 0 ≤ blochNorm ρ := Real.sqrt_nonneg _
  have hc : 0 ≤ l1Coherence ρ := by rw [hs]; positivity
  have he : blochNorm ρ = ‖bloch ρ‖ := by
    have hb : ‖bloch ρ‖ ^ 2 = blochNorm ρ ^ 2 := by
      rw [hsq, hs, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      change (2 * (ρ 0 1).re) ^ 2 + (-2 * (ρ 0 1).im) ^ 2 +
        ((ρ 0 0).re - (ρ 1 1).re) ^ 2 = _
      simp only [mul_pow, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re]
      ring
    nlinarith only [hb, hn, norm_nonneg (bloch ρ)]
  have hbound := norm_bloch_le_trace_of_posSemidef ρ hρ.1
  rw [hρ.2, Complex.one_re, ← he] at hbound
  refine ⟨hc, ?_, hbound, hsq⟩
  nlinarith only [hsq, hn, hc, sq_nonneg (ρ 0 0 - ρ 1 1).re]

private theorem measurement_bound {n : ℕ} (ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (hρ : IsDensity ρ) (e : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (he : IsPOVM e) :
    l1Coherence (luders e ρ) ≤ (l1Coherence ρ + blochNorm ρ) / 2 := by
  obtain ⟨k, z, v, hk, hs, hh, hf⟩ := luders_decomposition ρ hρ e he
  have hd := fun i => dephasing_bound (ρ 0 1) (z i) (v i) (ρ 0 0 - ρ 1 1).re
  let l := (l1Coherence ρ + blochNorm ρ) / 2
  have hc : 2 * ‖ρ 0 1‖ ≤ l := by
    have h := (radius_data ρ hρ).2.1
    rw [coherence_two ρ hρ.1.isHermitian] at h
    dsimp only [l]
    rw [coherence_two ρ hρ.1.isHermitian]
    linarith
  have hi (i : Fin n) :
      2 * ‖(k i : ℂ) * ρ 0 1 +
        ((2 * (star (z i) * ρ 0 1).re + v i * (ρ 0 0 - ρ 1 1).re : ℝ) : ℂ) * z i‖ ≤
      (k i + 2 * (‖z i‖ ^ 2 + v i ^ 2)) * l := by
    have ha := norm_add_le ((k i : ℂ) * ρ 0 1)
      (((2 * (star (z i) * ρ 0 1).re + v i * (ρ 0 0 - ρ 1 1).re : ℝ) : ℂ) * z i)
    rw [norm_mul, Complex.norm_of_nonneg (hk i)] at ha
    have hb := hd i
    change _ ≤ (‖z i‖ ^ 2 + v i ^ 2) * (2 * ‖ρ 0 1‖ + blochNorm ρ) at hb
    have hkc := mul_le_mul_of_nonneg_left hc (hk i)
    dsimp only [l] at *
    rw [coherence_two ρ hρ.1.isHermitian] at *
    nlinarith only [ha, hb, hkc]
  rw [coherence_two (luders e ρ) hh, hf]
  calc
    _ ≤ 2 * ∑ i, ‖(k i : ℂ) * ρ 0 1 +
        ((2 * (star (z i) * ρ 0 1).re + v i * (ρ 0 0 - ρ 1 1).re : ℝ) : ℂ) * z i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
    _ = ∑ i, 2 * ‖(k i : ℂ) * ρ 0 1 +
        ((2 * (star (z i) * ρ 0 1).re + v i * (ρ 0 0 - ρ 1 1).re : ℝ) : ℂ) * z i‖ :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ i, (k i + 2 * (‖z i‖ ^ 2 + v i ^ 2)) * l :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = l := by rw [← Finset.sum_mul, hs, one_mul]

private theorem phase_exists (c : ℂ) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ star a * c = (‖c‖ : ℂ) := by
  by_cases hc : c = 0
  · exact ⟨1, norm_one, by simp only [hc, mul_zero, norm_zero, Complex.ofReal_zero]⟩
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  refine ⟨c / (‖c‖ : ℂ), ?_, ?_⟩
  · rw [norm_div, Complex.norm_of_nonneg (norm_nonneg c), div_self hn]
  · rw [star_div₀, Complex.star_def, Complex.conj_ofReal, div_mul_eq_mul_div,
      ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    field_simp

private theorem optimal_axis (c : ℂ) (r : ℝ) :
    ∃ (z : ℂ) (v : ℝ), ‖z‖ ^ 2 + v ^ 2 = 1 ∧
      ‖((2 * (star z * c).re + v * r : ℝ) : ℂ) * z‖ =
        (2 * ‖c‖ + Real.sqrt (r ^ 2 + 4 * ‖c‖ ^ 2)) / 2 := by
  let s := 2 * ‖c‖
  let d := Real.sqrt (r ^ 2 + 4 * ‖c‖ ^ 2)
  let l := (s + d) / 2
  have hs : 0 ≤ s := by positivity
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hd : d ^ 2 = r ^ 2 + s ^ 2 := by
    have h := Real.sq_sqrt (show 0 ≤ r ^ 2 + 4 * ‖c‖ ^ 2 by positivity)
    dsimp only [d, s]
    nlinarith only [h]
  by_cases hdne : d = 0
  · have hr : r = 0 := by nlinarith only [hd, hdne, sq_nonneg s]
    have hc : c = 0 := by
      apply norm_eq_zero.mp
      dsimp only [s] at hd
      nlinarith only [hd, hdne, sq_nonneg r]
    subst c
    subst r
    exact ⟨1, 0, by norm_num, by norm_num⟩
  have hdpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hdne)
  have hl : 0 < l := by dsimp only [l]; linarith
  have hdisc : 4 * l * (l - s) = r ^ 2 := by dsimp only [l]; nlinarith only [hd]
  obtain ⟨a, ha, hac⟩ := phase_exists c
  let t := Real.sqrt (l / d)
  let v := r * t / (2 * l)
  let z := (t : ℂ) * a
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = l / d := Real.sq_sqrt (div_nonneg hl.le hd0)
  have hz : ‖z‖ = t := by
    dsimp only [z]
    rw [norm_mul, Complex.norm_of_nonneg ht, ha, mul_one]
  have hv : v ^ 2 = (l - s) / d := by
    dsimp only [v]
    rw [div_pow, mul_pow, ht2, ← hdisc]
    field_simp [hdne, hl.ne']
    ring
  have hunit : ‖z‖ ^ 2 + v ^ 2 = 1 := by
    rw [hz, ht2, hv, ← add_div]
    dsimp only [l]
    field_simp
    ring
  have hinner : (star z * c).re = t * ‖c‖ := by
    have hh : star z * c = ((t * ‖c‖ : ℝ) : ℂ) := by
      dsimp only [z]
      rw [star_mul, Complex.star_def, Complex.conj_ofReal]
      calc
        _ = (t : ℂ) * (star a * c) := by rw [Complex.star_def]; ring
        _ = _ := by rw [hac, Complex.ofReal_mul]
    rw [hh, Complex.ofReal_re]
  have hdot : 2 * (star z * c).re + v * r = d * t := by
    rw [hinner]
    have hf : 2 * (t * ‖c‖) = s * t := by dsimp only [s]; ring
    rw [hf]
    calc
      s * t + v * r = (s + r ^ 2 / (2 * l)) * t := by dsimp only [v]; ring
      _ = (s + 4 * l * (l - s) / (2 * l)) * t := by rw [← hdisc]
      _ = (2 * l - s) * t := by field_simp [hl.ne']; ring
      _ = d * t := by dsimp only [l]; ring
  refine ⟨z, v, hunit, ?_⟩
  change _ = l
  rw [hdot, norm_mul, Complex.norm_of_nonneg (mul_nonneg hd0 ht), hz]
  calc
    d * t * t = d * t ^ 2 := by ring
    _ = l := by rw [ht2]; field_simp

private def projector (z : ℂ) (v : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(((1 + v) / 2 : ℝ) : ℂ), z / 2; star z / 2, (((1 - v) / 2 : ℝ) : ℂ)]

private theorem projector_facts (z : ℂ) (v : ℝ) (hu : ‖z‖ ^ 2 + v ^ 2 = 1) :
    (projector z v).IsHermitian ∧ projector z v * projector z v = projector z v := by
  have hz : (z.re ^ 2 + z.im ^ 2) + v ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply] at hu
    nlinarith only [hu]
  constructor
  · change (projector z v)ᴴ = projector z v
    unfold projector
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> norm_num
  · unfold projector
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
      apply Complex.ext <;> norm_num <;> nlinarith only [hz]

private theorem padded_measurement {n : ℕ} (hn : 2 ≤ n)
    (p q ρ : Matrix (Fin 2) (Fin 2) ℂ) (hp : p.PosSemidef) (hq : q.PosSemidef)
    (hpp : p * p = p) (hqq : q * q = q) (hs : p + q = 1) :
    ∃ e : Fin n → Matrix (Fin 2) (Fin 2) ℂ, IsPOVM e ∧
      luders e ρ = p * ρ * p + q * ρ * q := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  let e : Fin (m + 2) → Matrix (Fin 2) (Fin 2) ℂ :=
    Fin.cons p (Fin.cons q (fun _ : Fin m => 0))
  have he (i : Fin (m + 2)) : (e i).PosSemidef :=
    Fin.cases hp (fun j => Fin.cases hq (fun _ => Matrix.PosSemidef.zero) j) i
  have hsum : ∑ i, e i = 1 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    change p + (q + ∑ _ : Fin m, (0 : Matrix (Fin 2) (Fin 2) ℂ)) = 1
    rw [Finset.sum_const_zero, add_zero, hs]
  refine ⟨e, ⟨he, hsum⟩, ?_⟩
  unfold luders
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  change CFC.sqrt p * ρ * CFC.sqrt p + (CFC.sqrt q * ρ * CFC.sqrt q +
    ∑ _ : Fin m, CFC.sqrt (0 : Matrix (Fin 2) (Fin 2) ℂ) * ρ * CFC.sqrt 0) = _
  rw [CFC.sqrt_unique hpp hp.nonneg, CFC.sqrt_unique hqq hq.nonneg]
  simp only [CFC.sqrt_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]

private theorem projector_output (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ)
    (z : ℂ) (v : ℝ) (hu : ‖z‖ ^ 2 + v ^ 2 = 1) :
    let p := projector z v
    l1Coherence (p * ρ * p + (1 - p) * ρ * (1 - p)) =
      ‖((2 * (star z * ρ 0 1).re + v * (ρ 0 0 - ρ 1 1).re : ℝ) : ℂ) * z‖ := by
  let p := projector z v
  have hp := (projector_facts z v hu).1
  have hq : (1 - p).IsHermitian := Matrix.isHermitian_one.sub hp
  have hh : (p * ρ * p + (1 - p) * ρ * (1 - p)).IsHermitian := by
    have ha := Matrix.isHermitian_mul_mul_conjTranspose p hρ.1.isHermitian
    have hb := Matrix.isHermitian_mul_mul_conjTranspose (1 - p) hρ.1.isHermitian
    rw [hp.eq] at ha
    rw [hq.eq] at hb
    exact ha.add hb
  have hr := hermitian_entries ρ hρ.1.isHermitian
  have hz : (z.re ^ 2 + z.im ^ 2) + v ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply] at hu
    nlinarith only [hu]
  have hf : (p * ρ * p + (1 - p) * ρ * (1 - p)) 0 1 =
      (((2 * (star z * ρ 0 1).re + v * (ρ 0 0 - ρ 1 1).re : ℝ) : ℂ) * z) / 2 := by
    dsimp only [p]
    unfold projector
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply]
    apply Complex.ext
    · norm_num [hr.2.2, hr.1, hr.2.1]
      linear_combination -(ρ 0 1).re / 2 * hz
    · norm_num [hr.2.2, hr.1, hr.2.1]
      linear_combination -(ρ 0 1).im / 2 * hz
  change l1Coherence (p * ρ * p + (1 - p) * ρ * (1 - p)) = _
  rw [coherence_two _ hh, hf, norm_div]
  norm_num
  ring

private theorem measurement_attainment {n : ℕ} (hn : 2 ≤ n)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ) :
    ∃ e : Fin n → Matrix (Fin 2) (Fin 2) ℂ, IsPOVM e ∧
      l1Coherence (luders e ρ) = (l1Coherence ρ + blochNorm ρ) / 2 := by
  obtain ⟨z, v, hu, hv⟩ := optimal_axis (ρ 0 1) (ρ 0 0 - ρ 1 1).re
  let p := projector z v
  let q := 1 - p
  have hp := (projector_facts z v hu).1
  have hpp : p * p = p := (projector_facts z v hu).2
  have hq : q.IsHermitian := Matrix.isHermitian_one.sub hp
  have hqq : q * q = q := by
    dsimp only [q]
    rw [sub_mul, one_mul, mul_sub, mul_one, hpp, sub_self, sub_zero]
  have hps : p.PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self p
    rwa [hp.eq, hpp] at h
  have hqs : q.PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self q
    rwa [hq.eq, hqq] at h
  have hs : p + q = 1 := by dsimp only [q]; abel
  obtain ⟨e, he, heq⟩ := padded_measurement hn p q ρ hps hqs hpp hqq hs
  refine ⟨e, he, ?_⟩
  rw [heq]
  change l1Coherence (p * ρ * p + (1 - p) * ρ * (1 - p)) = _
  rw [projector_output ρ hρ z v hu]
  rw [coherence_two ρ hρ.1.isHermitian]
  unfold blochNorm
  exact hv

private theorem zero_gain (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ) :
    (l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ = 0 ↔ ρ 0 0 = ρ 1 1 := by
  obtain ⟨hc, hcr, _, hsq⟩ := radius_data ρ hρ
  have hn : 0 ≤ blochNorm ρ := hc.trans hcr
  have he := hermitian_entries ρ hρ.1.isHermitian
  constructor
  · intro h
    have heq : blochNorm ρ = l1Coherence ρ := by linarith only [h]
    rw [heq] at hsq
    have hz : (ρ 0 0 - ρ 1 1).re = 0 := by nlinarith only [hsq]
    apply Complex.ext
    · simpa only [Complex.sub_re, sub_eq_zero] using hz
    · rw [he.1, he.2.1]
  · intro h
    rw [h, sub_self, Complex.zero_re, zero_pow (by decide : 2 ≠ 0), zero_add] at hsq
    nlinarith only [hsq, hn, hc]

private theorem maximal_gain (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ) :
    (l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ ≤ 1 / 2 ∧
      ((l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ = 1 / 2 ↔
        ρ = Matrix.diagonal ![1, 0] ∨ ρ = Matrix.diagonal ![0, 1]) := by
  obtain ⟨hc, hcr, hr, hsq⟩ := radius_data ρ hρ
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h
    have hc0 : l1Coherence ρ = 0 := by linarith
    have hr1 : blochNorm ρ = 1 := by linarith
    have hz : ρ 0 1 = 0 := by
      rw [coherence_two ρ hρ.1.isHermitian] at hc0
      exact norm_eq_zero.mp (by linarith)
    have he := hermitian_entries ρ hρ.1.isHermitian
    have h10 : ρ 1 0 = 0 := by rw [he.2.2, hz, star_zero]
    have ht : (ρ 0 0).re + (ρ 1 1).re = 1 := by
      have hh := congrArg Complex.re hρ.2
      rwa [Matrix.trace_fin_two, Complex.add_re] at hh
    have hd : (ρ 0 0 - ρ 1 1).re ^ 2 = 1 := by rw [hc0, hr1] at hsq; nlinarith
    rcases sq_eq_one_iff.mp hd with hd | hd
    · left
      have hp : (ρ 0 0).re = 1 ∧ (ρ 1 1).re = 0 := by
        rw [Complex.sub_re] at hd
        constructor <;> linarith
      ext i j
      fin_cases i <;> fin_cases j
      · change ρ 0 0 = 1
        apply Complex.ext <;> simp only [Complex.one_re, Complex.one_im] <;> tauto
      · exact hz
      · exact h10
      · change ρ 1 1 = 0
        apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im] <;> tauto
    · right
      have hp : (ρ 0 0).re = 0 ∧ (ρ 1 1).re = 1 := by
        rw [Complex.sub_re] at hd
        constructor <;> linarith
      ext i j
      fin_cases i <;> fin_cases j
      · change ρ 0 0 = 0
        apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im] <;> tauto
      · exact hz
      · exact h10
      · change ρ 1 1 = 1
        apply Complex.ext <;> simp only [Complex.one_re, Complex.one_im] <;> tauto
  · intro h
    rw [coherence_two ρ hρ.1.isHermitian]
    rcases h with rfl | rfl <;> unfold blochNorm <;> norm_num

/-- The attained maximum over all finite qubit POVMs, with both extremal gain criteria. -/
theorem result (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ)
    (n : ℕ) (hn : 2 ≤ n) :
    IsGreatest {c | ∃ e : Fin n → Matrix (Fin 2) (Fin 2) ℂ,
      IsPOVM e ∧ c = l1Coherence (luders e ρ)} ((l1Coherence ρ + blochNorm ρ) / 2) ∧
    ((l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ = 0 ↔ ρ 0 0 = ρ 1 1) ∧
    (l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ ≤ 1 / 2 ∧
    ((l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ = 1 / 2 ↔
      ρ = Matrix.diagonal ![1, 0] ∨ ρ = Matrix.diagonal ![0, 1]) := by
  obtain ⟨e, he, hv⟩ := measurement_attainment hn ρ hρ
  refine ⟨⟨⟨e, he, hv.symm⟩, ?_⟩, zero_gain ρ hρ, maximal_gain ρ hρ⟩
  rintro c ⟨f, hf, rfl⟩
  exact measurement_bound ρ hρ f hf

end D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum
