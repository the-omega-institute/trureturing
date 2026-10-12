/- GID: D5/S3/Quantum/Lieb/PowerConvexity
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/PowerConvexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compensated integral proof of dimension-independent operator power convexity. -/

import D5.S3.Quantum.Lieb.JensenOperatorInequality
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.Tactic.Module

/- Classical operator power convexity, using the pinned Mathlib integral
   representation and shifted inverse convexity. This closes the convex
   direction of the integral method; no mathematical originality is claimed. -/

noncomputable section
namespace D5.S3.Quantum.Lieb.PowerConvexity
universe u
open Set Real MeasureTheory
open scoped NNReal
variable {𝓐 : Type*} [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]

private lemma integrand_eq {p t : ℝ} (ht : 0 < t) {X : 𝓐} (hX : 0 ≤ X) :
    cfc (rpowIntegrand₁₂ p t) X =
      t ^ (p - 1) • (t⁻¹ • X + t • Ring.inverse (algebraMap ℝ 𝓐 t + X) - 1) := by
  have hg : ContinuousOn (fun z : ℝ => (t + z)⁻¹) (spectrum ℝ X) := by
    fun_prop (disch := grind)
  have hspectrum : ∀ z ∈ spectrum ℝ X, t + z ≠ 0 := by grind
  unfold rpowIntegrand₁₂
  rw [cfc_const_mul .., cfc_sub .., cfc_add .., cfc_const_mul .., cfc_id' ..,
    cfc_const_mul .., cfc_inv _ _ hspectrum .., cfc_const_add .., cfc_id' ..,
    cfc_const ..]
  simp only [map_one]

/-- The whole compensated kernel is convex; its individual terms are not integrated. -/
theorem convexOn_cfc_rpowIntegrand₁₂ {p t : ℝ} (ht : 0 < t) :
    ConvexOn ℝ (Ici (0 : 𝓐)) (cfc (rpowIntegrand₁₂ p t)) := by
  have heq : (Ici (0 : 𝓐)).EqOn (cfc (rpowIntegrand₁₂ p t))
      (fun X => t ^ (p - 1) •
        (t⁻¹ • X + t • Ring.inverse (algebraMap ℝ 𝓐 t + X) - 1)) :=
    fun _ hX => integrand_eq ht hX
  refine ConvexOn.congr ?_ heq.symm
  refine ConvexOn.smul (by positivity) ?_
  refine ConvexOn.sub ?_ (concaveOn_const (1 : 𝓐) (convex_Ici _))
  exact ((convexOn_id (convex_Ici _)).smul (by positivity)).add
    ((CStarAlgebra.convexOn_ringInverse_algebraMap_add ht).smul ht.le)

private lemma integrand_nonunital_eq {p t : ℝ} (ht : 0 < t) {X : 𝓐} (hX : 0 ≤ X) :
    cfcₙ (rpowIntegrand₁₂ p t) X = cfc (rpowIntegrand₁₂ p t) X := by
  refine cfcₙ_eq_cfc (hf := ?_) (hf0 := rpowIntegrand₁₂_zero ht)
  · unfold rpowIntegrand₁₂
    fun_prop (disch := grind)

private lemma convexOn_cfcₙ_rpowIntegrand₁₂ {p t : ℝ} (ht : 0 < t) :
    ConvexOn ℝ (Ici (0 : 𝓐)) (cfcₙ (rpowIntegrand₁₂ p t)) := by
  exact (convexOn_cfc_rpowIntegrand₁₂ ht).congr
    (fun _ hX => (integrand_nonunital_eq ht hX).symm)

private lemma convexOn_nnrpow_Ioo {p : ℝ≥0} (hp : p ∈ Ioo 1 2) :
    ConvexOn ℝ (Ici (0 : 𝓐)) (fun X => X ^ p) := by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂ 𝓐 hp
  have heq : (Ici (0 : 𝓐)).EqOn (fun X => X ^ p)
      (fun X => ∫ t in Ioi 0, cfcₙ (rpowIntegrand₁₂ p t) X ∂μ) :=
    fun X hX => (hμ X hX).2
  refine ConvexOn.congr ?_ heq.symm
  refine integral_convexOn_of_integrand_ae (convex_Ici _) ?_ fun X hX => (hμ X hX).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact convexOn_cfcₙ_rpowIntegrand₁₂ ht

private lemma convexOn_square :
    ConvexOn ℝ (Ici (0 : 𝓐)) (fun X => X * X) := by
  refine ⟨convex_Ici _, ?_⟩
  intro X hX Y hY s t hs ht hst
  have hsa : IsSelfAdjoint (X - Y) := hX.isSelfAdjoint.sub hY.isSelfAdjoint
  have hsq : 0 ≤ (X - Y) * (X - Y) := by
    simpa only [hsa.star_eq] using star_mul_self_nonneg (X - Y)
  have hid : s • (X * X) + t • (Y * Y) -
      (s • X + t • Y) * (s • X + t • Y) = (s * t) • ((X - Y) * (X - Y)) := by
    have hs' : s = 1 - t := by linarith
    rw [hs']
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      sub_mul, mul_sub]
    module
  exact sub_nonneg.mp (hid ▸ smul_nonneg (mul_nonneg hs ht) hsq)

/-- Spectral powers are operator convex on the positive cone for every 1 ≤ p ≤ 2,
in arbitrary complete ordered complex C-star algebras, including infinite dimension. -/
theorem convexOn_rpow {p : ℝ} (hp : p ∈ Icc 1 2) :
    ConvexOn ℝ (Ici (0 : 𝓐)) (fun X => CFC.rpow X p) := by
  by_cases hp1 : p = 1
  · subst p
    exact (convexOn_id (convex_Ici _)).congr (fun X hX => (CFC.rpow_one X hX).symm)
  by_cases hp2 : p = 2
  · subst p
    refine convexOn_square.congr ?_
    intro X hX
    simpa only [pow_two, Nat.cast_ofNat, ← CFC.rpow_eq_pow] using
      (CFC.rpow_natCast X 2 hX).symm
  have hp' : p ∈ Ioo 1 2 := ⟨lt_of_le_of_ne hp.1 (Ne.symm hp1), lt_of_le_of_ne hp.2 hp2⟩
  let q : ℝ≥0 := ⟨p, by linarith [hp.1]⟩
  have hq : q ∈ Ioo 1 2 := by exact_mod_cast hp'
  have hq0 : 0 < q := by exact_mod_cast (show 0 < p by linarith [hp.1])
  have hqp : (q : ℝ) = p := rfl
  have hh := convexOn_nnrpow_Ioo (𝓐 := 𝓐) hq
  simp only [CFC.nnrpow_eq_rpow hq0, ← CFC.rpow_eq_pow] at hh
  rwa [hqp] at hh

/-- The uniform Jensen input genuinely quantifies over every complete complex Hilbert space. -/
theorem condIciAll_rpow {p : ℝ} (hp : p ∈ Icc 1 2) :
    JensenOperatorInequality.CondIciAll.{u} (fun x : ℝ => x ^ p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K _ _ _ _
    intro X Y t hX hY ht0 ht1 hXs hYs
    have hX0 : (0 : LownerHeinzTheorem.L K) ≤ X :=
      (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) X (ha := hX)).2 hXs
    have hY0 : (0 : LownerHeinzTheorem.L K) ≤ Y :=
      (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) Y (ha := hY)).2 hYs
    have hm : 0 ≤ (1 - t) • X + t • Y :=
      add_nonneg (smul_nonneg (sub_nonneg.mpr ht1) hX0) (smul_nonneg ht0 hY0)
    have hh := (convexOn_rpow (𝓐 := LownerHeinzTheorem.L K) hp).2 hX0 hY0
      (sub_nonneg.mpr ht1) ht0 (by ring)
    change cfc (fun x : ℝ => x ^ p) ((1 - t) • X + t • Y) ≤
      (1 - t) • cfc (fun x : ℝ => x ^ p) X + t • cfc (fun x : ℝ => x ^ p) Y
    simpa only [CFC.rpow_eq_pow, ← CFC.rpow_eq_cfc_real hm, ← CFC.rpow_eq_cfc_real hX0,
      ← CFC.rpow_eq_cfc_real hY0] using hh
  · exact (Real.continuous_rpow_const (by linarith [hp.1])).continuousOn
  · simp only [Real.zero_rpow (by linarith [hp.1] : p ≠ 0), le_refl]

#print axioms convexOn_rpow
#print axioms condIciAll_rpow
end D5.S3.Quantum.Lieb.PowerConvexity
