/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite weighted sine polynomials control RH root increments. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootQuarterPhaseIncrement
import D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum

/-! The inclusive cutoff retains the analytic multiplicity of each positive zeta zero. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped BigOperators Topology ComplexConjugate

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (coeff_real)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit phaseOrbit_cluster_iff)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelGlobalStrictPositivity (weight)
open D5.S3.Weil.Mertens.ZeroAbscissaPower
  (actual_zero occurrence_finite_sum actual_high_weight counting_bound crypto_zero_iff)
open D5.S3.Weil.ZeroData
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness (PositiveZetaZero ordinate slope)
open D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum (zetaSpectrum)

private abbrev Count :=
  ConjectureMachines.Semantics.Riemann.VonMangoldtCount.weightedZeroCountingFunction
private abbrev gamma (k : ℕ) := (actualZero k).im

private theorem cutoff_occurrences_hasSum (T : ℝ) :
    HasSum (fun k : ℕ => if |gamma k| ≤ T then (1 : ℝ) else 0) (Count T : ℝ) := by
  classical
  open ConjectureMachines.Semantics.Riemann.VonMangoldtCount in
  have h := occurrence_finite_sum (nontrivialZetaZerosUpTo T)
    (fun z hz => (crypto_zero_iff z).mp (mem_nontrivialZetaZerosUpTo.mp hz).1)
    (fun _ => 1) (fun _ => zero_le_one)
  open ConjectureMachines.Semantics.Riemann.VonMangoldtCount in
  have heq (k : ℕ) : actualZero k ∈ nontrivialZetaZerosUpTo T ↔ |gamma k| ≤ T := by
    rw [mem_nontrivialZetaZerosUpTo]
    exact and_iff_right ((crypto_zero_iff _).mpr (actual_zero k))
  have h' := h.1.hasSum
  rw [h.2] at h'
  simpa only [heq, mul_one, Count,
    ConjectureMachines.Semantics.Riemann.VonMangoldtCount.weightedZeroCountingFunction,
    Nat.cast_sum] using h'

private abbrev leadingTerm (r t : ℝ) (p : ℕ → Circle) (k : ℕ) : ℂ :=
  (-(r : ℂ) * actualCoeff k) * (p k : ℂ) * phaseStep t k

private def linearTerm (r t : ℝ) (p : ℕ → Circle) (k : ℕ) : ℂ :=
  if |gamma k| ≤ t⁻¹ then
    (-(r : ℂ) * actualCoeff k) * (p k : ℂ) * ((gamma k * t : ℝ) * Complex.I)
  else 0

private theorem linear_term_summable (r : ℝ) {t : ℝ} (ht : 0 < t) (p : ℕ → Circle) :
    Summable (linearTerm r t p) := by
  apply Summable.of_norm_bounded (g := fun k => |r| * ‖actualCoeff k‖)
    (actualCoeff_hasSum.summable.norm.mul_left |r|)
  intro k
  unfold linearTerm
  split_ifs with hk
  · have hh : |gamma k| * t ≤ 1 := (le_div_iff₀ ht).mp (by simpa only [one_div] using hk)
    rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Circle.norm_coe, mul_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos ht]
    exact mul_le_of_le_one_right (by positivity) hh
  · simpa only [norm_zero] using (show 0 ≤ |r| * ‖actualCoeff k‖ by positivity)

set_option maxHeartbeats 600000 in
-- The pointwise low and high bounds use complex norms and real arithmetic.
private theorem leading_taylor (hRH : RiemannHypothesis) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ p : ℕ → Circle,
      |(∑' k, leadingTerm r t p k).re - (∑' k, linearTerm r t p k).re| ≤
        C * (t * (1 + Real.log t⁻¹)) := by
  classical
  obtain ⟨A, hA, hcount⟩ := counting_bound
  obtain ⟨B, hB, htail⟩ := actual_high_weight
  refine ⟨r * A + 2 * r * B, by positivity, ?_⟩
  intro t ht ht₂ p
  have hT : 2 ≤ t⁻¹ := by rw [inv_eq_one_div, le_div_iff₀ ht]; linarith
  let low (k : ℕ) : ℝ := if |gamma k| ≤ t⁻¹ then 1 else 0
  let high (k : ℕ) : ℝ := if t⁻¹ < |gamma k| then (gamma k)⁻¹ ^ 2 else 0
  have hinv : Summable (fun k : ℕ => (gamma k)⁻¹ ^ 2) := by
    simpa only [gamma, Function.comp_def, actualZero] using
      actualOccurrenceEquiv.summable_iff.mpr actual_sigma_inverse_square_summable
  have hhigh : Summable high := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hinv
    · dsimp only [high]; split_ifs <;> positivity
    · dsimp only [high]; split_ifs
      · exact le_rfl
      · positivity
  have hbound (k : ℕ) : ‖leadingTerm r t p k - linearTerm r t p k‖ ≤
      r * t ^ 2 * low k + 2 * r * high k := by
    let z : ℂ := (gamma k * t : ℝ) * Complex.I
    let a : ℂ := (-(r : ℂ) * actualCoeff k) * (p k : ℂ)
    have ha : ‖a‖ = r * weight k := by
      simp only [a, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        coeff_norm_eq_weight hRH, Circle.norm_coe, mul_one]
    by_cases hk : |gamma k| ≤ t⁻¹
    · have hz : ‖z‖ = |gamma k| * t := by
        simp only [z, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos ht]
      have hz₁ : ‖z‖ ≤ 1 := by
        rw [hz]
        exact (le_div_iff₀ ht).mp (by simpa only [one_div] using hk)
      have hweight : weight k * gamma k ^ 2 ≤ 1 := by
        unfold weight
        change 1 / (1 / 4 + gamma k ^ 2) * gamma k ^ 2 ≤ 1
        rw [one_div, inv_mul_eq_div]
        exact (div_le_one₀ (by positivity)).mpr (by linarith)
      simp only [leadingTerm, linearTerm, ite_eq_left hk, low, high, ite_eq_right (not_lt.mpr hk),
        mul_one, mul_zero, add_zero]
      change ‖a * (Complex.exp z - 1) - a * z‖ ≤ _
      rw [← mul_sub, norm_mul, ha]
      calc
        _ ≤ r * weight k * ‖z‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_sub_id_le hz₁)
            (by unfold weight; positivity)
        _ = r * t ^ 2 * (weight k * gamma k ^ 2) := by rw [hz, mul_pow, sq_abs]; ring
        _ ≤ _ := mul_le_of_le_one_right (by positivity) hweight
    · have hk' := lt_of_not_ge hk
      simp only [leadingTerm, linearTerm, ite_eq_right hk, low, high, ite_eq_left hk',
        sub_zero, mul_zero, zero_add]
      change ‖a * phaseStep t k‖ ≤ _
      rw [norm_mul, ha]
      calc
        _ ≤ r * weight k * 2 :=
          mul_le_mul_of_nonneg_left (norm_phaseStep_le t k) (by unfold weight; positivity)
        _ = 2 * r * weight k := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (weight_le_inverse_square k) (by positivity)
  have hlead : Summable (leadingTerm r t p) := leading_increment_summable r t p
  rw [← Complex.sub_re, ← hlead.tsum_sub (linear_term_summable r ht p)]
  apply (Complex.abs_re_le_norm _).trans
  refine (tsum_of_norm_bounded (((cutoff_occurrences_hasSum t⁻¹).mul_left (r * t ^ 2)).add
    (hhigh.hasSum.mul_left (2 * r))) hbound).trans ?_
  have h₁ := mul_le_mul_of_nonneg_left (hcount t⁻¹ hT) (show 0 ≤ r * t ^ 2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left (htail t⁻¹ hT) (show 0 ≤ 2 * r by positivity)
  have heq₁ : r * t ^ 2 * (A * t⁻¹ * (1 + Real.log t⁻¹)) =
      (r * A) * (t * (1 + Real.log t⁻¹)) := by field_simp
  have heq₂ : 2 * r * (B * (1 + Real.log t⁻¹) / t⁻¹) =
      (2 * r * B) * (t * (1 + Real.log t⁻¹)) := by rw [div_eq_mul_inv, inv_inv]; ring
  change r * t ^ 2 * (Count t⁻¹ : ℝ) + 2 * r * (∑' k, high k) ≤ _
  rw [heq₁] at h₁
  rw [heq₂] at h₂
  rw [add_mul]
  exact add_le_add h₁ h₂

/-- Analytic multiplicity times the harmonic weight of a positive zeta ordinate. -/
def harmonicWeight (j : PositiveZetaZero) : ℝ :=
  (Zeta23.zeroMult j.val : ℝ) * ordinate j / (1 / 4 + (ordinate j) ^ 2)

/-- The finite set of positive zeta zeros with ordinate at most the cutoff. -/
def positiveCutoff (hRH : RiemannHypothesis) (T : ℝ) : Finset PositiveZetaZero :=
  (zetaSpectrum hRH).cut T

/-- The harmonic mass of the actual positive zeros through the inclusive cutoff. -/
def harmonicMass (hRH : RiemannHypothesis) (T : ℝ) : ℝ :=
  ∑ j ∈ positiveCutoff hRH T, harmonicWeight j

/-- The finite sine polynomial with the same analytic-multiplicity weights as the mass. -/
def weightedSine (hRH : RiemannHypothesis) (T v : ℝ) : ℝ :=
  ∑ j ∈ positiveCutoff hRH T, harmonicWeight j * Real.sin (ordinate j * v)

private theorem linear_term_eq (hRH : RiemannHypothesis) (r : ℝ) {t : ℝ}
    (ht : 0 < t) (p : ℕ → Circle) (f : ℝ → ℝ)
    (hf : ∀ x, f (-x) = -f x) (hp : ∀ k, (p k : ℂ).im = f (gamma k)) :
    (∑' k, linearTerm r t p k).re =
      (2 * r * t) * ∑ j ∈ positiveCutoff hRH t⁻¹, harmonicWeight j * f (ordinate j) := by
  classical
  let g (z : ℂ) : ℝ :=
    if |z.im| ≤ t⁻¹ then r * t * (z.im / (1 / 4 + z.im ^ 2)) * f z.im else 0
  have hg (k : ℕ) : (linearTerm r t p k).re = g (actualZero k) := by
    by_cases hk : |gamma k| ≤ t⁻¹
    · simp only [linearTerm, ite_eq_left hk, g, coeff_real hRH, Complex.mul_re, Complex.mul_im,
        Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, hp]
      dsimp only [gamma] at *
      ring
    · change ¬ |(actualZero k).im| ≤ t⁻¹ at hk
      simp only [linearTerm, g, gamma, ite_eq_right hk, Complex.zero_re]
  have hconj (z : ℂ) : g (conj z) = g z := by
    simp only [g, Complex.conj_im, abs_neg, neg_sq, hf, neg_div]
    split_ifs <;> ring
  have hsum := (Complex.hasSum_re (linear_term_summable r ht p).hasSum).congr_fun
    (fun k => (hg k).symm)
  rw [← hsum.tsum_eq, tsum_occurrences_eq_twice_positive g hconj hsum.summable,
    tsum_eq_sum (s := positiveCutoff hRH t⁻¹)]
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hle : ordinate j ≤ t⁻¹ := ((zetaSpectrum hRH).finite_le t⁻¹).mem_toFinset.mp hj
    change j.val.im ≤ t⁻¹ at hle
    simp only [g, abs_of_pos j.property.2, ite_eq_left hle, harmonicWeight, ordinate]
    ring
  · intro j hj
    have hnot : ¬ordinate j ≤ t⁻¹ := fun h =>
      hj (((zetaSpectrum hRH).finite_le t⁻¹).mem_toFinset.mpr h)
    change ¬j.val.im ≤ t⁻¹ at hnot
    simp only [g, abs_of_pos j.property.2, ite_eq_right hnot, mul_zero]

private theorem root_signal_weighted_sine_estimate (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r) :
    let s : ℝ := 1 / 2 - (2 * r)⁻¹
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ (Real.exp 1)⁻¹ → ∀ u : ℝ,
      |rootSignal r (u + h) - rootSignal r u -
        (2 * h / s) * weightedSine hRH (r / h) (u / r)| ≤ C * (h * Real.log (1 / h)) := by
  dsimp only
  have hr₀ : 0 < r := by linarith
  let s : ℝ := 1 / 2 - (2 * r)⁻¹
  let D : ℝ := r * (r - 1) * ∑' k, ‖actualCoeff k‖
  have hs : 0 < s := by
    dsimp only [s]
    rw [inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  have hD : 0 ≤ D :=
    mul_nonneg (by positivity) (tsum_nonneg fun _ => norm_nonneg _)
  obtain ⟨B, hB, hTaylor⟩ := leading_taylor hRH hr₀
  refine ⟨((D + B) / s / r) * (2 + Real.log r), by
    have := Real.log_nonneg hr.le
    positivity, ?_⟩
  intro h hh hh₁ u
  let t := h / r
  let v := u / r
  have ht : 0 < t := div_pos hh hr₀
  have hrt : r * t = h := by dsimp only [t]; field_simp
  have hrv : r * v = u := by dsimp only [v]; field_simp
  have htinv : t⁻¹ = r / h := by dsimp only [t]; rw [inv_div]
  have hlogh : 1 ≤ Real.log (1 / h) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (1 / h) := Real.log_le_log (Real.exp_pos 1) (by
        rw [one_div]
        exact (le_inv_comm₀ (Real.exp_pos _) hh).mpr hh₁)
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hh₂ : h ≤ 1 / 2 :=
    hh₁.trans (by simpa only [one_div] using
      (inv_le_inv₀ (Real.exp_pos 1) (show (0 : ℝ) < 2 by norm_num)).mpr hexp)
  have ht₂ : t ≤ 1 / 2 := (div_le_self hh.le hr.le).trans hh₂
  have hT : 2 ≤ t⁻¹ := by rw [inv_eq_one_div, le_div_iff₀ ht]; linarith
  have hlogt : 0 ≤ Real.log t⁻¹ := Real.log_nonneg (by linarith)
  have hdt : D * t ≤ D * (t * (1 + Real.log t⁻¹)) := by
    nlinarith only [mul_nonneg (mul_nonneg hD ht.le) hlogt]
  have hlog : Real.log t⁻¹ = Real.log r + Real.log (1 / h) := by
    rw [htinv, Real.log_div hr₀.ne' hh.ne', one_div, Real.log_inv, sub_eq_add_neg]
  have hlog_le : 1 + Real.log t⁻¹ ≤ (2 + Real.log r) * Real.log (1 / h) := by
    rw [hlog]
    nlinarith only [mul_nonneg (Real.log_nonneg hr.le) (sub_nonneg.mpr hlogh), hlogh]
  have hpoly := linear_term_eq hRH r ht (phaseOrbit v) (fun γ => Real.sin (γ * v))
    (fun x => by rw [neg_mul, Real.sin_neg])
    (fun k => by
      simp only [phaseOrbit, Circle.coe_exp, Complex.exp_ofReal_mul_I_im, gamma, mul_comm v])
  have hpoly' : (∑' k, linearTerm r t (phaseOrbit v) k).re =
      (2 * h * weightedSine hRH (r / h) v) := by
    rw [hpoly, htinv, show 2 * r * t = 2 * h by linear_combination 2 * hrt]
    rfl
  have hinc : increment r t (phaseOrbit v) = rootSignal r (u + h) - rootSignal r u := by
    simp only [increment, read_signal_orbit hRH hr, hrv, hrt, add_zero]
  have he := increment_close_to_leading hRH hr t (phaseOrbit v)
  dsimp only at he
  change |s * increment r t (phaseOrbit v) - (∑' k, leadingTerm r t (phaseOrbit v) k).re| ≤
    D * |t| at he
  rw [hinc, abs_of_pos ht] at he
  have htail := hTaylor t ht ht₂ (phaseOrbit v)
  rw [hpoly'] at htail
  have hc := (abs_sub_le (s * (rootSignal r (u + h) - rootSignal r u))
    (∑' k, leadingTerm r t (phaseOrbit v) k).re ((2 * h * weightedSine hRH (r / h) v))).trans
      (add_le_add he htail)
  have hscale : s * (rootSignal r (u + h) - rootSignal r u -
      (2 * h / s) * weightedSine hRH (r / h) v) =
      s * (rootSignal r (u + h) - rootSignal r u) -
        (2 * h * weightedSine hRH (r / h) v) := by
    field_simp [hs.ne']
  change |rootSignal r (u + h) - rootSignal r u - (2 * h / s) * weightedSine hRH (r / h) v| ≤ _
  apply le_of_mul_le_mul_left _ hs
  rw [← abs_of_pos hs, ← abs_mul, abs_of_pos hs, hscale]
  calc
    _ ≤ (D + B) * (t * (1 + Real.log t⁻¹)) := by rw [add_mul]; linarith only [hc, hdt]
    _ ≤ (D + B) * (t * ((2 + Real.log r) * Real.log (1 / h))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog_le ht.le) (add_nonneg hD hB)
    _ = _ := by dsimp only [t]; field_simp

private theorem harmonic_mass_error (hRH : RiemannHypothesis) :
    ∃ A C : ℝ, 2 ≤ A ∧ 0 ≤ C ∧ ∀ T : ℝ, A ≤ T →
      |harmonicMass hRH T - (1 / (4 * Real.pi)) * (Real.log T) ^ 2| ≤
        C * (1 + Real.log T) := by
  obtain ⟨A, B, hA, hB, hslope⟩ :=
    ZetaOrdinatePhaseStiffness.actual_zeta_phase_stiffness.2.2.2.2
  obtain ⟨C, hC, hTaylor⟩ := leading_taylor hRH (show (0 : ℝ) < 1 by norm_num)
  refine ⟨A, (B + C) / 2, hA, by positivity, ?_⟩
  intro T hT
  have hT₀ : 0 < T := by linarith
  let t : ℝ := T⁻¹
  have ht : 0 < t := inv_pos.mpr hT₀
  have ht₂ : t ≤ 1 / 2 := by
    rw [one_div]
    exact (inv_le_inv₀ hT₀ (show (0 : ℝ) < 2 by norm_num)).mpr (hA.trans hT)
  have htA : A * |t| ≤ 1 := by
    rw [abs_of_pos ht, show t = 1 / T by exact (one_div T).symm, mul_one_div, div_le_one₀ hT₀]
    exact hT
  have htinv : t⁻¹ = T := inv_inv T
  have hval : (∑' k, leadingTerm 1 t occurrenceQuarter k).re = slope t := by
    simpa only [leadingTerm, one_mul] using (quarter_sine_hasSum hRH 1 t).2
  have hlinear : (∑' k, linearTerm 1 t occurrenceQuarter k).re = 2 * t * harmonicMass hRH T := by
    have hf (x : ℝ) : (-x) / |-x| = -(x / |x|) := by rw [abs_neg, neg_div]
    have hp (k : ℕ) : (occurrenceQuarter k : ℂ).im = gamma k / |gamma k| := by
      change (if 0 < gamma k then Complex.I else -Complex.I).im = gamma k / |gamma k|
      by_cases hk : 0 < gamma k
      · rw [ite_eq_left hk, Complex.I_im, abs_of_pos hk, div_self hk.ne']
      · have hk₀ : gamma k ≠ 0 := abs_pos.mp
          ((by norm_num : (0 : ℝ) < 10).trans (actual_height_gt_ten _ (actual_zero k)))
        have hk' := lt_of_le_of_ne (le_of_not_gt hk) hk₀
        rw [ite_eq_right hk, Complex.neg_im, Complex.I_im, abs_of_neg hk', div_neg, div_self hk₀]
    rw [linear_term_eq hRH 1 ht occurrenceQuarter (fun x => x / |x|) hf hp, htinv, mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hj : 0 < ordinate j := j.property.2
    rw [abs_of_pos hj, div_self hj.ne', mul_one]
  have h₁ := hTaylor t ht ht₂ occurrenceQuarter
  rw [hval, hlinear, htinv, abs_sub_comm] at h₁
  have h₂ := (hslope t (by rwa [abs_of_pos ht]) htA).2
  rw [abs_of_pos ht, htinv] at h₂
  have h₃ := (abs_sub_le (2 * t * harmonicMass hRH T) (slope t)
    ((1 / (2 * Real.pi)) * t * (Real.log T) ^ 2)).trans (add_le_add h₁ h₂)
  have hmain : (1 / (2 * Real.pi)) * t * (Real.log T) ^ 2 =
      (2 * t) * ((1 / (4 * Real.pi)) * (Real.log T) ^ 2) := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [hmain, ← mul_sub, abs_mul, abs_of_pos (show 0 < 2 * t by positivity)] at h₃
  apply le_of_mul_le_mul_left _ (show 0 < 2 * t by positivity)
  exact h₃.trans_eq (by ring)

/-- The multiplicity-weighted harmonic mass has leading coefficient 1 / (4π). -/
theorem harmonic_mass_limit (hRH : RiemannHypothesis) :
    Tendsto (fun T : ℝ => harmonicMass hRH T / (Real.log T) ^ 2) atTop
      (𝓝 (1 / (4 * Real.pi))) := by
  obtain ⟨A, C, hA, hC, hbound⟩ := harmonic_mass_error hRH
  have hlog : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hrate : Tendsto (fun T : ℝ => C * (((Real.log T)⁻¹)^2 + (Real.log T)⁻¹))
      atTop (𝓝 0) := by
    simpa using (((hlog.pow 2).add hlog).const_mul C)
  have hd : Tendsto (fun T : ℝ => harmonicMass hRH T / (Real.log T)^2 - 1 / (4 * Real.pi))
      atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ hrate
    filter_upwards [eventually_ge_atTop A] with T hT
    have hlog₀ : 0 < Real.log T := Real.log_pos (by linarith)
    have h := div_le_div_of_nonneg_right (hbound T hT) (sq_nonneg (Real.log T))
    calc
      _ = |(harmonicMass hRH T - (1 / (4 * Real.pi)) * (Real.log T)^2) / (Real.log T)^2| := by
        congr 1
        field_simp [hlog₀.ne', Real.pi_ne_zero]
      _ = |harmonicMass hRH T - (1 / (4 * Real.pi)) * (Real.log T)^2| / (Real.log T)^2 := by
        rw [abs_div, abs_of_nonneg (sq_nonneg (Real.log T))]
      _ ≤ C * (1 + Real.log T) / (Real.log T)^2 := h
      _ = _ := by field_simp [hlog₀.ne']
  simpa using hd.add_const (1 / (4 * Real.pi))

#print axioms harmonic_mass_limit

/-- The real supremum of the weighted sine polynomial over all real times. -/
def weightedSineSup (hRH : RiemannHypothesis) (T : ℝ) : ℝ :=
  sSup (range (weightedSine hRH T))

private theorem weighted_sine_abs_le_mass (hRH : RiemannHypothesis) (T v : ℝ) :
    |weightedSine hRH T v| ≤ harmonicMass hRH T := by
  unfold weightedSine harmonicMass
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hj : 0 < ordinate j := j.property.2
  have hw : 0 ≤ harmonicWeight j := by unfold harmonicWeight; positivity
  rw [abs_mul, abs_of_nonneg hw]
  exact mul_le_of_le_one_right hw (Real.abs_sin_le_one _)

theorem weighted_sine_bddAbove (hRH : RiemannHypothesis) (T : ℝ) :
    BddAbove (range (weightedSine hRH T)) :=
  ⟨harmonicMass hRH T, fun _ ⟨v, hv⟩ => hv ▸
    (le_abs_self (weightedSine hRH T v)).trans (weighted_sine_abs_le_mass hRH T v)⟩

theorem weighted_sine_sup_bounds (hRH : RiemannHypothesis) (T : ℝ) :
    0 ≤ weightedSineSup hRH T ∧ weightedSineSup hRH T ≤ harmonicMass hRH T := by
  refine ⟨?_, csSup_le (range_nonempty _) ?_⟩
  · have h := le_csSup (weighted_sine_bddAbove hRH T) (mem_range_self (0 : ℝ))
    simpa only [weightedSineSup, weightedSine, mul_zero, Real.sin_zero,
      Finset.sum_const_zero] using h
  · rintro _ ⟨v, rfl⟩
    exact (le_abs_self _).trans (weighted_sine_abs_le_mass hRH T v)

private theorem weighted_sine_abs_le_sup (hRH : RiemannHypothesis) (T v : ℝ) :
    |weightedSine hRH T v| ≤ weightedSineSup hRH T := by
  have hodd : weightedSine hRH T (-v) = -weightedSine hRH T v := by
    simp only [weightedSine, mul_neg, Real.sin_neg, Finset.sum_neg_distrib]
  apply abs_le.mpr
  refine ⟨?_, le_csSup (weighted_sine_bddAbove hRH T) (mem_range_self v)⟩
  exact neg_le.mp (hodd ▸ le_csSup (weighted_sine_bddAbove hRH T) (mem_range_self (-v)))

private theorem weighted_sine_cluster (hRH : RiemannHypothesis) (T v : ℝ) :
    MapClusterPt (weightedSine hRH T v) atTop (weightedSine hRH T) := by
  have hex (j : PositiveZetaZero) : ∃ k, actualZero k = j.val := by
    obtain ⟨n, hn⟩ := actualData.zero_exhaustive j.property.1
    refine ⟨actualOccurrenceEquiv.symm ⟨n, ⟨0, actualData.multiplicity_pos n⟩⟩, ?_⟩
    simpa only [actualZero, Equiv.apply_symm_apply] using hn
  let k (j : PositiveZetaZero) : ℕ := (hex j).choose
  let read (p : ℕ → Circle) : ℝ :=
    ∑ j ∈ positiveCutoff hRH T, harmonicWeight j * (p (k j) : ℂ).im
  have hcont : Continuous read := by
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul (Complex.continuous_im.comp
      (continuous_subtype_val.comp (continuous_apply (k j))))
  have hread (x : ℝ) : read (phaseOrbit x) = weightedSine hRH T x := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [phaseOrbit, Circle.coe_exp, Complex.exp_ofReal_mul_I_im, k,
      (hex j).choose_spec, ordinate, mul_comm x]
  have horbit := (phaseOrbit_cluster_iff (phaseOrbit v)).2 (subset_closure (mem_range_self v))
  simpa only [Function.comp_def, hread] using horbit.continuousAt_comp hcont.continuousAt

/-- Oddness gives the uniform absolute upper estimate. Actual orbit recurrence gives
arbitrarily late signed values above every strict threshold below the matching lower estimate. -/
theorem root_signal_weighted_sine_return (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r) :
    let s : ℝ := 1 / 2 - (2 * r)⁻¹
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ (Real.exp 1)⁻¹ →
      let P := (2 * h / s) * weightedSineSup hRH (r / h)
      let E := C * (h * Real.log (1 / h))
      (∀ u : ℝ, |rootSignal r (u + h) - rootSignal r u| ≤ P + E) ∧
        ∀ U b : ℝ, b < P - E → ∃ u ≥ U, b < rootSignal r (u + h) - rootSignal r u := by
  dsimp only
  obtain ⟨C, hC, hTaylor⟩ := root_signal_weighted_sine_estimate hRH hr
  refine ⟨C, hC, ?_⟩
  intro h hh hh'
  let s : ℝ := 1 / 2 - (2 * r)⁻¹
  let a := 2 * h / s
  let T := r / h
  let E := C * (h * Real.log (1 / h))
  have hr₀ : 0 < r := zero_lt_one.trans hr
  have hs : 0 < s := by
    dsimp only [s]
    rw [inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  have ha : 0 < a := by dsimp only [a]; positivity
  change (∀ u, |rootSignal r (u + h) - rootSignal r u| ≤ a * weightedSineSup hRH T + E) ∧
    ∀ U b, b < a * weightedSineSup hRH T - E →
      ∃ u ≥ U, b < rootSignal r (u + h) - rootSignal r u
  constructor
  · intro u
    have hpoly := mul_le_mul_of_nonneg_left
      (weighted_sine_abs_le_sup hRH T (u / r)) ha.le
    have hpoly' : |a * weightedSine hRH T (u / r)| ≤ a * weightedSineSup hRH T := by
      rwa [abs_mul, abs_of_pos ha]
    exact (abs_sub_le (rootSignal r (u + h)) (rootSignal r u + a * weightedSine hRH T (u / r))
      (rootSignal r u)).trans (by
        rw [sub_add_eq_sub_sub, add_sub_cancel_left]
        exact (add_le_add (hTaylor h hh hh' u) hpoly').trans_eq (add_comm _ _))
  · intro U b hb
    have hb' : (b + E) / a < weightedSineSup hRH T :=
      (div_lt_iff₀ ha).2 (by linarith only [hb])
    obtain ⟨_, ⟨v, rfl⟩, hv⟩ := exists_lt_of_lt_csSup (range_nonempty _) hb'
    have hret := (weighted_sine_cluster hRH T v).frequently (eventually_gt_nhds hv)
    obtain ⟨x, hx, hxlate⟩ := (hret.and_eventually (eventually_ge_atTop (U / r))).exists
    have hux : r * x / r = x := by field_simp
    have hdiff := (abs_le.mp (hTaylor h hh hh' (r * x))).1
    change -E ≤ rootSignal r (r * x + h) - rootSignal r (r * x) -
      a * weightedSine hRH T (r * x / r) at hdiff
    rw [hux] at hdiff
    exact ⟨r * x, ((div_le_iff₀ hr₀).1 hxlate).trans_eq (mul_comm _ _),
      by linarith only [hdiff, (div_lt_iff₀ ha).1 hx]⟩

#print axioms root_signal_weighted_sine_return

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
