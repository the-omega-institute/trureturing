/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Genuine radial differentiation of all original signed external columns. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalMoments

/-! Polynomial-geometric derivative bounds act on the original vector series. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology ENNReal
open Filter
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadial
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianWeightedResolvent
open OriginalGaussianAllIndexResolvent OriginalGaussianDifferentiation
open OriginalGaussianExternalResolvent OriginalGaussianExternalFrequency
open OriginalGaussianBilinearTranspose OriginalGaussianExternalDisplacement

private def externalCoefficient (out : Bool) (p n : ℕ) : H :=
  lp.single 2 n (-(Real.sqrt (n + 1 : ℝ) : ℂ) * externalBinomial out p (n + 1))

private lemma externalCoefficient_bound (out : Bool) (p n : ℕ) :
    ‖externalCoefficient out p n‖ ≤ (p + 1 : ℝ) ^ p * (n + 1 : ℝ) ^ (p + 1) := by
  simpa only [externalCoefficient, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),
    externalColumn, one_pow, mul_one] using
    externalColumn_bound out p (by norm_num : (0 : ℝ) ≤ 1)
      (z := 1) (by norm_num : ‖(1 : ℂ)‖ ≤ 1) n

private def externalTerm (out : Bool) (p : ℕ) (z : ℂ) (n : ℕ) : H :=
  z ^ (n + 1) • externalCoefficient out p n

private def externalDerivativeTerm (out : Bool) (p : ℕ) (z : ℂ) (n : ℕ) : H :=
  ((n + 1 : ℂ) * z ^ n) • externalCoefficient out p n

def externalDerivative (out : Bool) (p : ℕ) (z : ℂ) : H :=
  ∑' n : ℕ, externalDerivativeTerm out p z n

private lemma externalTerm_eq (out : Bool) (p : ℕ) (z : ℂ) (n : ℕ) :
    externalTerm out p z n = lp.single 2 n (externalColumn out p z n) := by
  rw [externalTerm, externalCoefficient, ← lp.single_smul]
  congr 1
  simp only [externalColumn, smul_eq_mul]
  ring

private lemma derivative_bound (out : Bool) (p : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖externalDerivativeTerm out p z n‖ ≤
      (p + 1 : ℝ) ^ p * (n + 1 : ℝ) ^ (p + 2) * R ^ n := by
  have hn : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
    exact_mod_cast Complex.norm_natCast (n + 1)
  simp only [externalDerivativeTerm, norm_smul, norm_mul, norm_pow, hn]
  calc
    _ ≤ ((n + 1 : ℝ) * R ^ n) *
        ((p + 1 : ℝ) ^ p * (n + 1 : ℝ) ^ (p + 1)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n)
          (by positivity)) (externalCoefficient_bound out p n) (norm_nonneg _) (by positivity)
    _ = _ := by rw [show p + 2 = (p + 1) + 1 by omega, pow_succ]; ring

private lemma derivative_summable (out : Bool) (p : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖externalDerivativeTerm out p z n‖) := by
  obtain ⟨R, hzR, hR1⟩ := exists_between hz
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg z) hzR
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (derivative_bound out p hR.le hzR.le)
  simpa only [mul_assoc] using
    (derivative_shifted_geometric hR hR1 (p + 2)).mul_left ((p + 1 : ℝ) ^ p)

/-- Complex differentiation of each complete original external vector, for all signed modes. -/
theorem hasDerivAt_externalVector (out : Bool) (p : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (externalVector out p) (externalDerivative out p z) z := by
  obtain ⟨R, hzR, hR1⟩ := exists_between hz
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg z) hzR
  have hm : z ∈ Metric.ball (0 : ℂ) R := by simpa using hzR
  have hd (n : ℕ) (w : ℂ) : HasDerivAt (fun w => externalTerm out p w n)
      (externalDerivativeTerm out p w n) w := by
    simpa only [externalTerm, externalDerivativeTerm, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using
      (hasDerivAt_pow (n + 1) w).smul_const (externalCoefficient out p n)
  have hs : Summable (fun n : ℕ => externalTerm out p z n) := by
    simp_rw [externalTerm_eq]
    apply Summable.of_norm
    simpa only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] using
      (externalColumn_l1 out p (norm_nonneg z) hz le_rfl).2
  have h := hasDerivAt_tsum_of_isPreconnected
    ((derivative_shifted_geometric hR hR1 (p + 2)).mul_left ((p + 1 : ℝ) ^ p))
    Metric.isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected
    (fun n w _ => hd n w) (fun n w hw => by
      simpa only [mul_assoc] using derivative_bound out p hR.le
        (by simpa using (Metric.mem_ball.mp hw).le) n) hm hs hm
  convert! h using 1
  · ext w
    simp only [externalTerm_eq, externalVector]

private lemma derivative_frequency (out : Bool) (p : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    z • externalDerivative out p z = frequencyVector out p z := by
  ext n
  change z * (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n)
    (∑' k : ℕ, externalDerivativeTerm out p z k) = _
  rw [(lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).map_tsum (derivative_summable out p hz).of_norm,
    tsum_eq_single n]
  · rw [frequencyVector_apply out p hz]
    change z * (((n + 1 : ℂ) * z ^ n) *
      (lp.single (E := fun _ : ℕ => ℂ) 2 n
        (-(Real.sqrt (n + 1 : ℝ) : ℂ) * externalBinomial out p (n + 1))) n) = _
    simp only [lp.single_apply, Pi.single_eq_same, externalColumn, pow_succ]
    ring
  · intro k hk
    change (((k + 1 : ℂ) * z ^ k) *
      (lp.single (E := fun _ : ℕ => ℂ) 2 k
        (-(Real.sqrt (k + 1 : ℝ) : ℂ) * externalBinomial out p (k + 1))) n) = 0
    simp [lp.single_apply, hk]

/-- The real radial derivative uses exactly the original frequency vector. -/
theorem hasDerivAt_radial_externalVector (out : Bool) (p : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun u : ℝ => externalVector out p (Real.sqrt u : ℂ))
      ((1 / (2 * (r : ℂ))) • frequencyVector out p (Real.sqrt r : ℂ)) r := by
  have h := (hasDerivAt_externalVector out p (radial_norm_lt_one hr1)).scomp r
    (Real.hasDerivAt_sqrt hr.ne').ofReal_comp
  apply h.congr_deriv
  rw [← derivative_frequency out p (radial_norm_lt_one hr1), smul_smul]
  change (((1 / (2 * Real.sqrt r) : ℝ) : ℂ)) • _ = _
  congr 1
  have hz : (Real.sqrt r : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hr).ne'
  have hs : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt hr.le
  push_cast
  rw [← hs]
  field_simp [hz]

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadial
