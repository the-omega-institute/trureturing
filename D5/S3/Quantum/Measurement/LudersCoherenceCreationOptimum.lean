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
  simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, zero_add, add_zero, Fin.zero_ne_one, (by decide : (1 : Fin 2) ≠ 0),
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
      simp only [Matrix.mul_apply, Fin.sum_univ_two, h00 i, h11 i, h10 i, hr.2.2] <;>
      change _ = _
    · dsimp only [k, v]
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
        Complex.conj_im, zero_mul, mul_zero, sub_zero, zero_add, hr.1, hr.2.1]
      rw [hzsq i]
      change _ = _
      dsimp only [z]
      linear_combination (p i + q i) * (m i 0 1).re / 2 * hx
    · dsimp only [k, v]
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
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

private theorem measurement_attainment {n : ℕ} (hn : 2 ≤ n)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ) :
    ∃ e : Fin n → Matrix (Fin 2) (Fin 2) ℂ, IsPOVM e ∧
      l1Coherence (luders e ρ) = (l1Coherence ρ + blochNorm ρ) / 2 := by
  sorry

private theorem zero_gain (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ) :
    (l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ = 0 ↔ ρ 0 0 = ρ 1 1 := by
  sorry

private theorem maximal_gain (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ) :
    (l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ ≤ 1 / 2 ∧
      ((l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ = 1 / 2 ↔
        ρ = Matrix.diagonal ![1, 0] ∨ ρ = Matrix.diagonal ![0, 1]) := by
  sorry

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
