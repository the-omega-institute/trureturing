/- GID: D5/S3/Quantum/Recovery/LiebOverlapPetzEquality
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LiebOverlapPetzEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual power-overlap equality characterizes fixed Petz recovery. -/

import D5.S3.Quantum.Divergence.LiebOverlapResolventIntegralBudget
import D5.S3.Quantum.Recovery.CanonicalPetzEquality
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
Actual equality theorem for the physical overlap and a single fixed recovery.
proof_shape: content; admission_basis: escape-witness.

The recovery channel is chosen from Phi and sigma before rho and q. The only
physical hypotheses are finite nonempty systems, density states, support
containment and 0<q<1. No spectral floor, physical sharpness or novelty is claimed.

The proof consumes the original inverse-continuity and contraction-saturation
suppliers, Mathlib's integral zero criterion and its continuity-on-open-set
AE-to-pointwise theorem. It reuses the existing completed Petz channel.
-/

noncomputable section
universe u v
open Matrix Set MeasureTheory Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
open D5.S3.Quantum.Divergence.LiebOverlapResolventIntegralBudget
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Recovery.CanonicalPetzEquality

namespace D5.S3.Quantum.Recovery.LiebOverlapPetzEquality

private def overlap {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : DensityState n) (q : ℝ) : ℝ :=
  (cfc (fun x : ℝ => x ^ (1 - q)) (CStarMatrix.ofMatrix.symm rho.1) *
    cfc (fun x : ℝ => x ^ q) (CStarMatrix.ofMatrix.symm sigma.1)).trace.re

private theorem overlap_mono
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Phi : QuantumChannel a b) (rho sigma : DensityState a)
    (support : SupportContained rho sigma) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    overlap rho sigma q ≤ overlap (Phi.mapState rho) (Phi.mapState sigma) q := by
  classical
  let M := supported_relative_modular_model Phi rho sigma support
  let w : ℝ → EuclideanSpace ℂ (M.data.J × M.data.I) := fun t => WithLp.toLp 2
    ((M.data.A + t • 1)⁻¹ *ᵥ M.data.ξ -
      M.data.V *ᵥ ((M.data.B + t • 1)⁻¹ *ᵥ M.data.η))
  obtain ⟨hi, hb⟩ := actual_lieb_overlap_resolvent_integral_budget
    Phi rho sigma support q hq0 hq1
  change (∫ t in Ioi (0 : ℝ), t ^ (q + 1) * ‖w t‖ ^ 2) ≤
    (overlap (Phi.mapState rho) (Phi.mapState sigma) q - overlap rho sigma q) /
      (Real.sin (Real.pi * q) / Real.pi) at hb
  have hnonneg : 0 ≤ ∫ t in Ioi (0 : ℝ), t ^ (q + 1) * ‖w t‖ ^ 2 := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (sq_nonneg _)
  have hsin : 0 < Real.sin (Real.pi * q) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hq0)
      (by simpa using mul_lt_mul_of_pos_left hq1 Real.pi_pos)
  have hnormalizer := div_pos hsin Real.pi_pos
  have hgap := (le_div_iff₀ hnormalizer).mp (hnonneg.trans hb)
  simpa only [zero_mul, sub_nonneg] using hgap

private theorem overlap_equality_forces_entropy_equality
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Phi : QuantumChannel a b) (rho sigma : DensityState a)
    (support : SupportContained rho sigma) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (heq : overlap (Phi.mapState rho) (Phi.mapState sigma) q = overlap rho sigma q) :
    finiteTraceLogRelativeEntropy rho sigma =
      finiteTraceLogRelativeEntropy (Phi.mapState rho) (Phi.mapState sigma) := by
  classical
  let M := supported_relative_modular_model Phi rho sigma support
  let z : ℝ → (M.data.J × M.data.I → ℂ) := fun t =>
    (M.data.A + t • 1)⁻¹ *ᵥ M.data.ξ -
      M.data.V *ᵥ ((M.data.B + t • 1)⁻¹ *ᵥ M.data.η)
  let w : ℝ → EuclideanSpace ℂ (M.data.J × M.data.I) := fun t => WithLp.toLp 2 (z t)
  let E : ℝ → ℝ := fun t => t ^ (q + 1) * ‖w t‖ ^ 2
  have hbudget := actual_lieb_overlap_resolvent_integral_budget
    Phi rho sigma support q hq0 hq1
  change IntegrableOn E (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), E t) ≤
      (overlap (Phi.mapState rho) (Phi.mapState sigma) q - overlap rho sigma q) /
        (Real.sin (Real.pi * q) / Real.pi) at hbudget
  obtain ⟨hEi, hb⟩ := hbudget
  have hb0 : (∫ t in Ioi (0 : ℝ), E t) ≤ 0 := by
    simpa only [heq, sub_self, zero_div] using hb
  have hE0 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] E := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (sq_nonneg _)
  have hInt0 : (∫ t in Ioi (0 : ℝ), E t) = 0 :=
    le_antisymm hb0 (integral_nonneg_of_ae hE0)
  have hEae : E =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hE0 hEi).mp hInt0

  -- The original positive-shift inverse continuity supplier is reused in place.
  have hEcont : ContinuousOn E (Ioi (0 : ℝ)) := by
    intro t ht
    have hIA := D5.S3.Quantum.Divergence.EntropyDefectResolventIntegralBudget.continuousAt_shift_inverse M.data.A M.hA.posSemidef t ht
    have hIB := D5.S3.Quantum.Divergence.EntropyDefectResolventIntegralBudget.continuousAt_shift_inverse M.data.B M.hB.posSemidef t ht
    have hpow : Continuous (fun s : ℝ => s ^ (q + 1)) :=
      Real.continuous_rpow_const (by linarith)
    have hc : ContinuousAt
        (fun s : ℝ => s ^ (q + 1) * (star (z s) ⬝ᵥ z s).re) t := by
      dsimp only [z, Matrix.mulVec, dotProduct]
      fun_prop
    simpa only [E, w, l2_norm_sq] using hc.continuousWithinAt
  have hEpoint : EqOn E 0 (Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hEae isOpen_Ioi hEcont continuousOn_const
  have hwzero (t : ℝ) (ht : 0 < t) :
      (M.data.A + t • 1)⁻¹ *ᵥ M.data.ξ =
        M.data.V *ᵥ ((M.data.B + t • 1)⁻¹ *ᵥ M.data.η) := by
    have he : t ^ (q + 1) * ‖w t‖ ^ 2 = 0 := hEpoint ht
    have hsq : ‖w t‖ ^ 2 = 0 :=
      (mul_eq_zero.mp he).resolve_left (Real.rpow_pos_of_pos ht _).ne'
    have hn : ‖w t‖ = 0 := by nlinarith [norm_nonneg (w t)]
    have hw : w t = 0 := norm_eq_zero.mp hn
    have hz : z t = 0 := by
      simpa [w] using congrArg WithLp.ofLp hw
    exact sub_eq_zero.mp hz

  -- Norm saturation is essential; the original supplier already proves it.
  have hsaturation :
      (star (M.data.V *ᵥ M.data.η) ⬝ᵥ (M.data.V *ᵥ M.data.η)).re =
        (star M.data.η ⬝ᵥ M.data.η).re := by
    rw [M.mapsη, ← l2_norm_sq, ← l2_norm_sq,
      EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, M.normξ, M.normη]
  have hadjoint : M.data.Vᴴ *ᵥ M.data.ξ = M.data.η := by
    have h := D5.S3.Quantum.Divergence.ResolventDefectRigidity.contraction_saturation
      M.data.V M.hVnorm M.data.η hsaturation
    simpa only [M.mapsη] using h
  have pair (y : M.data.L × M.data.K → ℂ) :
      star M.data.ξ ⬝ᵥ (M.data.V *ᵥ y) =
        star (M.data.Vᴴ *ᵥ M.data.ξ) ⬝ᵥ y := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.conjTranspose_conjTranspose]
  have hGzero (t : ℝ) (ht : 0 < t) :
      (star (M.data.V *ᵥ M.data.η) ⬝ᵥ
        ((M.data.A + t • 1)⁻¹ *ᵥ (M.data.V *ᵥ M.data.η))).re -
      (star M.data.η ⬝ᵥ ((M.data.B + t • 1)⁻¹ *ᵥ M.data.η)).re = 0 := by
    rw [M.mapsη, hwzero t ht, pair, hadjoint, sub_self]
  have hfunctional := D5.S3.Quantum.Divergence.ResolventFunctionalRigidity.zero_resolvent_defects_force_functional_intertwining
      M.data.A M.data.B M.hA.posSemidef M.hB.posSemidef
      M.data.V M.hVnorm M.hVA M.data.η hsaturation hGzero Real.log
  have hlog : (star M.data.ξ ⬝ᵥ (cfc Real.log M.data.A *ᵥ M.data.ξ)).re =
      (star M.data.η ⬝ᵥ (cfc Real.log M.data.B *ᵥ M.data.η)).re := by
    rw [M.mapsη] at hfunctional
    rw [hfunctional, pair, hadjoint]
  exact M.canonicalTraceR.trans ((congrArg Neg.neg hlog).trans M.canonicalTraceT.symm)

/-- The same completed Petz channel, chosen before rho and q, characterizes
both actual Petz-overlap equality and actual relative-entropy equality. -/
theorem actual_lieb_overlap_equality_iff_fixed_petz_recovery
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Phi : QuantumChannel a b) (sigma : DensityState a) :
    let K := (actual_kraus_representation Phi).kraus
    let S := cfc Real.sqrt (CStarMatrix.ofMatrix.symm sigma.1)
    let Q := CStarMatrix.ofMatrix.symm (Phi.mapState sigma).1
    let W := spectralInverseSqrt Q
    let P := spectralSupport Q
    ∃ recovery : QuantumChannel b a,
      (∀ X : Matrix b b ℂ,
        CStarMatrix.ofMatrix.symm
          (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          (∑ c, S * (K c)ᴴ * W * X * W * K c * S) +
            Matrix.trace ((1 - P) * X) • CStarMatrix.ofMatrix.symm sigma.1) ∧
      recovery.mapState (Phi.mapState sigma) = sigma ∧
      ∀ (rho : DensityState a) (_support : SupportContained rho sigma)
        (q : ℝ), 0 < q → q < 1 →
        let inputOverlap := (cfc (fun x : ℝ => x ^ (1 - q))
            (CStarMatrix.ofMatrix.symm rho.1) *
          cfc (fun x : ℝ => x ^ q) (CStarMatrix.ofMatrix.symm sigma.1)).trace.re
        let outputOverlap := (cfc (fun x : ℝ => x ^ (1 - q))
            (CStarMatrix.ofMatrix.symm (Phi.mapState rho).1) *
          cfc (fun x : ℝ => x ^ q)
            (CStarMatrix.ofMatrix.symm (Phi.mapState sigma).1)).trace.re
        (outputOverlap = inputOverlap ↔
          finiteTraceLogRelativeEntropy rho sigma =
            finiteTraceLogRelativeEntropy (Phi.mapState rho) (Phi.mapState sigma)) ∧
        (outputOverlap = inputOverlap ↔ recovery.mapState (Phi.mapState rho) = rho) := by
  classical
  dsimp only
  obtain ⟨recovery, haction, hreference, hEntropy⟩ :=
    supported_entropy_equality_iff_fixed_petz_recovery Phi sigma
  refine ⟨recovery, haction, hreference, ?_⟩
  intro rho support q hq0 hq1
  change (overlap (Phi.mapState rho) (Phi.mapState sigma) q = overlap rho sigma q ↔
      finiteTraceLogRelativeEntropy rho sigma =
        finiteTraceLogRelativeEntropy (Phi.mapState rho) (Phi.mapState sigma)) ∧
    (overlap (Phi.mapState rho) (Phi.mapState sigma) q = overlap rho sigma q ↔
      recovery.mapState (Phi.mapState rho) = rho)
  have hforward := overlap_equality_forces_entropy_equality Phi rho sigma support q hq0 hq1
  have hrecovery (h : recovery.mapState (Phi.mapState rho) = rho) :
      overlap (Phi.mapState rho) (Phi.mapState sigma) q = overlap rho sigma q := by
    have hm := overlap_mono Phi rho sigma support q hq0 hq1
    have hr := overlap_mono recovery (Phi.mapState rho) (Phi.mapState sigma)
      (supported_relative_modular_model Phi rho sigma support).outputSupport q hq0 hq1
    rw [h, hreference] at hr
    exact le_antisymm hr hm
  have hEntropyIff := hEntropy rho support
  refine ⟨⟨hforward, ?_⟩, ⟨?_, hrecovery⟩⟩
  · intro h
    exact hrecovery (hEntropyIff.mp h)
  · intro h
    exact hEntropyIff.mp (hforward h)

#print axioms actual_lieb_overlap_equality_iff_fixed_petz_recovery

end D5.S3.Quantum.Recovery.LiebOverlapPetzEquality
