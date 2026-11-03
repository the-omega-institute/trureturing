/- GID: D5/S3/Quantum/Divergence/EntropyDefectInversePowerStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/EntropyDefectInversePowerStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual entropy loss controls every supported inverse fractional power in L2. -/

import D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
import D5.S3.Analytic.Interpolation.CapWeightedEnergy

/-! Fractional supported modular stability with the sharp abstract cap-energy constant.

The scalar normalizer and finite spectral integral are consumed through the generalized
implementation in EntropyDefectInverseSqrtStability. The present theorem consumes the
actual canonical model and actual entropy deficit, with all norms in EuclideanSpace.
proof_shape: content; escape_witness: CapWeightedEnergy.norm_integral_le_sharp_cap_energy;
admission_basis: escape-witness. This is a repository derivation, with no literature-novelty claim.
All declarations are general bounds, with no certified numerical instance, enumeration,
checker, or numerical reduction; utility kind is none.
-/

noncomputable section
universe u v
open Matrix Set MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Topology
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
open D5.S3.Analytic.Interpolation

namespace D5.S3.Quantum.Divergence.EntropyDefectInversePowerStability

/-- Actual entropy loss controls supported inverse fractional-power intertwining,
with the best constant available from the abstract cap and energy hypotheses. -/
theorem entropy_defect_inverse_power_stability
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Φ : QuantumChannel a b) (ρ σ : DensityState a) (support : SupportContained ρ σ)
    (m : ℝ) (hm : 0 < m) (alpha : ℝ) (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    let M := supported_relative_modular_model Φ ρ σ support
    m • 1 ≤ M.data.A → m • 1 ≤ M.data.B →
    let d := cfc (fun x : ℝ => x ^ (-alpha)) M.data.A *ᵥ M.data.ξ -
      M.data.V *ᵥ (cfc (fun x : ℝ => x ^ (-alpha)) M.data.B *ᵥ M.data.η)
    Real.sqrt (star d ⬝ᵥ d).re ≤
      (Real.sin (Real.pi * alpha) / Real.pi) * CapWeightedEnergy.sharpConstant alpha *
        (2 / m) ^ alpha *
        (finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) ^
            ((1 - alpha) / 2) := by
  classical
  let M := supported_relative_modular_model Φ ρ σ support
  change m • 1 ≤ M.data.A → m • 1 ≤ M.data.B → _
  intro hfloorA hfloorB
  let w : ℝ → EuclideanSpace ℂ (M.data.J × M.data.I) := fun t => WithLp.toLp 2
    ((M.data.A + t • 1)⁻¹ *ᵥ M.data.ξ -
      M.data.V *ᵥ ((M.data.B + t • 1)⁻¹ *ᵥ M.data.η))
  let d := cfc (fun x : ℝ => x ^ (-alpha)) M.data.A *ᵥ M.data.ξ -
    M.data.V *ᵥ (cfc (fun x : ℝ => x ^ (-alpha)) M.data.B *ᵥ M.data.η)
  let delta := finiteTraceLogRelativeEntropy ρ σ -
    finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)
  have hnξ : ‖(WithLp.toLp 2 M.data.ξ : EuclideanSpace ℂ (M.data.J × M.data.I))‖ = 1 := by
    have h := M.normξ
    rw [← EuclideanSpace.norm_sq_eq (WithLp.toLp 2 M.data.ξ)] at h
    nlinarith [norm_nonneg (WithLp.toLp 2 M.data.ξ : EuclideanSpace ℂ (M.data.J × M.data.I))]
  have hnη : ‖(WithLp.toLp 2 M.data.η : EuclideanSpace ℂ (M.data.L × M.data.K))‖ = 1 := by
    have h := M.normη
    rw [← EuclideanSpace.norm_sq_eq (WithLp.toLp 2 M.data.η)] at h
    nlinarith [norm_nonneg (WithLp.toLp 2 M.data.η : EuclideanSpace ℂ (M.data.L × M.data.K))]
  have hcap (t : ℝ) (ht : 0 < t) : ‖w t‖ ≤ 2 / m := by
    have hA := l2_resolvent_bound M.data.A M.hA m hm hfloorA M.data.ξ t ht
    have hB := l2_resolvent_bound M.data.B M.hB m hm hfloorB M.data.η t ht
    rw [hnξ] at hA
    rw [hnη] at hB
    have hV := l2_contraction M.data.V M.hVnorm ((M.data.B + t • 1)⁻¹ *ᵥ M.data.η)
    change ‖(WithLp.toLp 2 ((M.data.A + t • 1)⁻¹ *ᵥ M.data.ξ) :
      EuclideanSpace ℂ (M.data.J × M.data.I)) -
      WithLp.toLp 2 (M.data.V *ᵥ ((M.data.B + t • 1)⁻¹ *ᵥ M.data.η))‖ ≤ _
    exact (norm_sub_le _ _).trans ((add_le_add hA (hV.trans hB)).trans_eq (by ring))
  obtain ⟨hE, hbudget⟩ :=
    EntropyDefectResolventIntegralBudget.entropy_defect_resolvent_integral_budget Φ ρ σ support
  have hE' : IntegrableOn (fun t : ℝ => t * ‖w t‖ ^ 2) (Ioi 0) := by
    simpa only [w, l2_norm_sq] using hE
  have hbudget' : (∫ t in Ioi (0 : ℝ), t * ‖w t‖ ^ 2) ≤ delta := by
    simpa only [w, delta, l2_norm_sq] using hbudget
  have hE0 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun t => t * ‖w t‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg ht.le (sq_nonneg _)
  have hdelta : 0 ≤ delta := (integral_nonneg_of_ae hE0).trans hbudget'
  obtain ⟨hi, he⟩ := l2_inverse_power_integral alpha ⟨halpha0, halpha1⟩
    M.data.A M.data.B M.hA M.hB M.data.V M.data.ξ M.data.η
  have hw : AEStronglyMeasurable w (volume.restrict (Ioi (0 : ℝ))) := by
    have h := (Real.continuous_rpow_const halpha0.le).aestronglyMeasurable.smul
      hi.aestronglyMeasurable
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change t ^ alpha • (t ^ (-alpha) • w t) = w t
    rw [smul_smul, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, one_smul]
  obtain ⟨_, hsharp⟩ := CapWeightedEnergy.norm_integral_le_sharp_cap_energy
    w alpha (2 / m) delta halpha0 halpha1 (by positivity) hdelta hw
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hcap t ht)) hE' hbudget'
  have hc : 0 ≤ Real.sin (Real.pi * alpha) / Real.pi :=
    div_nonneg (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos halpha0)
      (by simpa using mul_lt_mul_of_pos_left halpha1 Real.pi_pos)).le Real.pi_pos.le
  have hnorm : Real.sqrt (star d ⬝ᵥ d).re =
      ‖(WithLp.toLp 2 d : EuclideanSpace ℂ (M.data.J × M.data.I))‖ := by
    rw [← l2_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  change Real.sqrt (star d ⬝ᵥ d).re ≤ _
  rw [hnorm, ← he, norm_smul, Real.norm_of_nonneg hc]
  simpa only [mul_assoc, delta] using mul_le_mul_of_nonneg_left hsharp hc

#print axioms entropy_defect_inverse_power_stability

end D5.S3.Quantum.Divergence.EntropyDefectInversePowerStability
