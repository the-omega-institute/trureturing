/- GID: D5/S3/Weil/ZetaAnalytic/WhiteFloorSamplingDuality
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaAnalytic/WhiteFloorSamplingDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A spectral quadratic identity equates the white floor with the least sampling bound. -/

import D5.S3.Weil.ZetaAnalytic.LocalSpectralFloor

/- Library-search audit trail (2026-08-29):
   * D5 searches for white-floor sampling duality, unit-sphere sampling
     infima, and normalized Rayleigh quotients found no exact theorem.
   * `LocalSpectralFloor.white_noise_cone_margin` is the canonical D5 owner
     of the cone-margin-to-Rayleigh-infimum identity and is applied directly.
   * Body-shape searches for the cone-margin supremum and unit-norm sampling
     value set found only that adjacent cone-margin theorem.
   * Pinned Mathlib supplies scalar norm and continuous-linear-map laws but no
     packaged equality between the nonzero Rayleigh and unit-sphere infima. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaAnalytic.WhiteFloorSamplingDuality

open Set
open D5.S3.Weil.ZetaAnalytic.LocalSpectralFloor

/-- If the local quadratic form is represented by a linear sampling analysis
operator, its maximal nonnegative white floor is the least squared sampling
norm on the unit sphere. -/
theorem white_floor_sampling_frame_duality
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace Real H] [Nontrivial H]
    [NormedAddCommGroup K] [NormedSpace Real K]
    (quadratic : H -> Real) (sampling : H →L[Real] K)
    (spectralIdentity : forall f, quadratic f = ‖sampling f‖ ^ 2) :
    let whiteFloors :=
      {lambda : Real | forall f, 0 <= quadratic f - lambda * ‖f‖ ^ 2}
    let samplingBounds :=
      {r : Real | exists f, ‖f‖ = 1 /\ r = ‖sampling f‖ ^ 2}
    sSup whiteFloors = sInf samplingBounds := by
  dsimp only
  let rayleighValues : Set Real :=
    {r | exists f, f ≠ 0 /\ r = quadratic f / ‖f‖ ^ 2}
  let whiteFloors : Set Real :=
    {lambda | forall f, 0 <= quadratic f - lambda * ‖f‖ ^ 2}
  let samplingBounds : Set Real :=
    {r | exists f, ‖f‖ = 1 /\ r = ‖sampling f‖ ^ 2}
  have quadraticZero : quadratic 0 = 0 := by
    rw [spectralIdentity]
    simp
  have normSqZero : ‖(0 : H)‖ ^ 2 = 0 := by simp
  have normSqPositive : forall f : H, f ≠ 0 -> 0 < ‖f‖ ^ 2 := by
    intro f hf
    positivity
  have rayleighBounded : BddBelow rayleighValues := by
    refine ⟨0, ?_⟩
    rintro value ⟨f, hf, rfl⟩
    rw [spectralIdentity]
    positivity
  have coneMargin : sInf rayleighValues = sSup whiteFloors := by
    exact white_noise_cone_margin quadratic (fun f : H => ‖f‖ ^ 2)
      quadraticZero normSqZero normSqPositive rayleighBounded
  have rayleighValuesEq : rayleighValues = samplingBounds := by
    ext value
    constructor
    · rintro ⟨f, hf, rfl⟩
      let unit : H := ‖f‖⁻¹ • f
      have normNonzero : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
      have unitNorm : ‖unit‖ = 1 := by
        simp [unit, norm_smul, normNonzero]
      refine ⟨unit, unitNorm, ?_⟩
      rw [spectralIdentity]
      simp only [unit, map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_norm]
      field_simp [normNonzero]
    · rintro ⟨f, unitNorm, rfl⟩
      have hf : f ≠ 0 := by
        intro fZero
        subst f
        simp at unitNorm
      refine ⟨f, hf, ?_⟩
      rw [spectralIdentity, unitNorm]
      norm_num
  calc
    sSup whiteFloors = sInf rayleighValues := coneMargin.symm
    _ = sInf samplingBounds := congrArg sInf rayleighValuesEq

example :
    let sampling : Real →L[Real] Real :=
      ContinuousLinearMap.id Real Real
    let quadratic : Real -> Real := fun x => ‖x‖ ^ 2
    forall f, quadratic f = ‖sampling f‖ ^ 2 := by
  simp

#print axioms white_floor_sampling_frame_duality

end D5.S3.Weil.ZetaAnalytic.WhiteFloorSamplingDuality
