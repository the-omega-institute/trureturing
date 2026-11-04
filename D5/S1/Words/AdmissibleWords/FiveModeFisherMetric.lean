/- GID: D5/S1/Words/AdmissibleWords/FiveModeFisherMetric
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/FiveModeFisherMetric
   mirror-E: none(waiver:analytically-proved)
   anchors: []
   utility: none
   digest: The affine five-mode simplex carries its actual smooth Fisher tangent metric. -/

import D5.S1.Words.AdmissibleWords.FiveModeFisherImmersion
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/- The classical categorical Fisher construction is consumed
   on the actual four-dimensional affine chart. No RH transport is asserted. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.FiveModeFisherMetric

open scoped Manifold ContDiff Topology Bundle
open Bundle Manifold ContinuousLinearMap
open D5.S1.Words.AdmissibleWords.FiveModeFisherImmersion
open D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates

abbrev Coordinates := Fin 4 → ℝ

def simplexDomain : TopologicalSpace.Opens Coordinates :=
  ⟨chartDomain, five_mode_fisher_chart_immersion.1⟩

abbrev FiveModeManifold := simplexDomain

/-- The Fisher form as an actual continuous bilinear map. -/
def fisherMetricForm (q : Coordinates) : Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ :=
  ∑ s : Fin 5, (simplexLaw q s)⁻¹ •
    (((ContinuousLinearMap.proj s).comp tangentLift).smulRight
      ((ContinuousLinearMap.proj s).comp tangentLift))

private theorem fisherMetricForm_eq (q : Coordinates) (u v : Coordinates) :
    fisherMetricForm q u v = fisher (simplexLaw q) (tangentLift u) (tangentLift v) := by
  simp only [fisherMetricForm, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, fisher]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [div_eq_mul_inv]
  ring

private theorem fisherMetricForm_contDiffOn :
    ContDiffOn ℝ ∞ fisherMetricForm chartDomain := by
  apply ContDiffOn.sum
  intro s _hs
  have hcoord : ContDiff ℝ ∞ (fun q : Coordinates => simplexLaw q s) :=
    (contDiff_apply ℝ (fun _ : Fin 5 => ℝ) s).comp
      (tangentLift.contDiff.add contDiff_const)
  exact (hcoord.contDiffOn.inv (fun q hq => (hq s).ne')).smul contDiffOn_const

private theorem fisherMetricForm_isVonNBounded (q : FiveModeManifold) :
    Bornology.IsVonNBounded ℝ {u : Coordinates | fisherMetricForm q u u < 1} := by
  classical
  apply (NormedSpace.isVonNBounded_iff' ℝ).2
  refine ⟨1, ?_⟩
  intro u hu
  change fisherMetricForm (q : Coordinates) u u < 1 at hu
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  have hp : simplexLaw q ∈ openSimplex :=
    (five_mode_fisher_chart_immersion.2.1 q).1 q.property
  have hpi : simplexLaw q i.succ ≤ 1 := by
    calc
      simplexLaw q i.succ ≤ ∑ s, simplexLaw q s :=
        Finset.single_le_sum (fun s _ => (hp.1 s).le) (Finset.mem_univ _)
      _ = 1 := hp.2
  rw [fisherMetricForm_eq] at hu
  have hpart : tangentLift u i.succ * tangentLift u i.succ /
      simplexLaw q i.succ ≤ fisher (simplexLaw q) (tangentLift u) (tangentLift u) :=
    Finset.single_le_sum (fun s _ => div_nonneg (mul_self_nonneg _) (hp.1 s).le)
      (Finset.mem_univ _)
  have hsmall := lt_of_le_of_lt hpart hu
  have hsquare := (div_lt_one (hp.1 i.succ)).1 hsmall
  have hcoord : tangentLift u i.succ = u i := by simp [tangentLift]
  rw [hcoord] at hsquare
  rw [Real.norm_eq_abs]
  exact (sq_le_one_iff_abs_le_one _).1 (by nlinarith only [hsquare, hpi])

private theorem tangent_chart_eq (a b : FiveModeManifold) :
    achart Coordinates a = achart Coordinates b := by
  rfl

private theorem tangent_symmL_id (a b : FiveModeManifold) :
    (trivializationAt Coordinates (TangentSpace 𝓘(ℝ, Coordinates)) a).symmL ℝ b =
      (1 : Coordinates →L[ℝ] Coordinates) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core]
  · rw [tangent_chart_eq a b]
    apply ContinuousLinearMap.ext
    intro v
    change _ = v
    exact (tangentBundleCore 𝓘(ℝ, Coordinates) FiveModeManifold).coordChange_self
      (achart Coordinates b) b (mem_achart_source Coordinates b) v
  · rw [show chartAt Coordinates a = chartAt Coordinates b from rfl]
    exact mem_chart_source Coordinates b

private theorem fisherMetricForm_contMDiff :
    ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ) ∞
      (fun q : FiveModeManifold => fisherMetricForm q) :=
  fisherMetricForm_contDiffOn.contMDiffOn.comp_contMDiff
    contMDiff_subtype_val (fun q => q.property)

/-- A genuine smooth Fisher metric on the actual four-dimensional tangent bundle. -/
def fisherRiemannianMetric :
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, Coordinates) ∞ Coordinates
      (fun q : FiveModeManifold => TangentSpace 𝓘(ℝ, Coordinates) q) where
  inner q := fisherMetricForm q
  symm q u v := by
    change fisherMetricForm (q : Coordinates) (u : Coordinates) (v : Coordinates) =
      fisherMetricForm (q : Coordinates) (v : Coordinates) (u : Coordinates)
    rw [fisherMetricForm_eq, fisherMetricForm_eq]
    apply Finset.sum_congr rfl
    intro s _hs
    rw [mul_comm]
  pos q u hu := by
    change 0 < fisherMetricForm (q : Coordinates) (u : Coordinates) (u : Coordinates)
    rw [fisherMetricForm_eq]
    exact (five_mode_fisher_chart_immersion.2.2.2.2 q q.property).2.2.2.2 u hu
  isVonNBounded q := by
    change Bornology.IsVonNBounded ℝ {u : Coordinates | fisherMetricForm q u u < 1}
    exact fisherMetricForm_isVonNBounded q
  contMDiff := by
    intro q
    rw [contMDiffAt_section]
    convert! fisherMetricForm_contMDiff q using 1
    funext b
    ext u v
    have ht : b ∈ (trivializationAt Coordinates
        (TangentSpace 𝓘(ℝ, Coordinates)) q).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet,
        show chartAt Coordinates q = chartAt Coordinates b from rfl]
      exact mem_chart_source Coordinates b
    simp only [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂ ht ht (by simp)]
    rw [← Trivialization.symmL_apply (R := ℝ) _ ht,
      ← Trivialization.symmL_apply (R := ℝ) _ ht]
    simp [tangent_symmL_id]
    rfl

instance fisherRiemannianBundle :
    RiemannianBundle (fun q : FiveModeManifold => TangentSpace 𝓘(ℝ, Coordinates) q) :=
  ⟨fisherRiemannianMetric.toRiemannianMetric⟩

#synth IsContMDiffRiemannianBundle 𝓘(ℝ, Coordinates) ∞ Coordinates
  (fun q : FiveModeManifold => TangentSpace 𝓘(ℝ, Coordinates) q)

#synth IsContinuousRiemannianBundle Coordinates
  (fun q : FiveModeManifold => TangentSpace 𝓘(ℝ, Coordinates) q)

#print axioms fisherRiemannianMetric

end D5.S1.Words.AdmissibleWords.FiveModeFisherMetric
