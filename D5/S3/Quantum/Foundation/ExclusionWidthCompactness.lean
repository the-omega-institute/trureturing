/- GID: D5/S3/Quantum/Foundation/ExclusionWidthCompactness
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ExclusionWidthCompactness
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.KreinMilman]
   utility: none
   digest: Full-effect widths and common-zero limits of entire exclusion balls. -/

import D5.S3.Quantum.Foundation.ContinuousFrameSum
import D5.S3.Quantum.Foundation.OriginalFacePolarity
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.SeparatingDual

noncomputable section
open Set Filter Topology

namespace D5.S3.Quantum.Foundation.ExclusionWidthCompactness

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces ContinuousFrameSum

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- All original confirming effects, including their entire continuous representation. -/
def confirmingEffects (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p : V) :
    Set (V →L[ℝ] ℝ) := {f | f ∈ effects C u ∧ f p = 1}

/-- Oscillation on the whole specified set. -/
def oscillation (F : Set V) (f : V →L[ℝ] ℝ) : ℝ :=
  sSup (f '' F) - sInf (f '' F)

/-- Width over the entire original effect interval. -/
def width (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (F : Set V) : ℝ :=
  sSup (oscillation F '' effects C u)

private theorem unit_proper (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) : proper C u u := by
  intro x hx
  refine ⟨?_, le_rfl⟩
  by_cases hz : x = 0
  · simp [hz]
  · exact (hs x hx hz).le

/-- The minimum over every original confirmer is attained, also at mixed inputs. -/
theorem comparison_attained
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (p : pure C u) (x : V) :
    ∃ f : V →L[ℝ] ℝ, f ∈ confirmingEffects C u p ∧ comparison C u p x = f x := by
  have hF : IsCompact (confirmingEffects C u p) :=
    (effects_compact hs hg).inter_right (isClosed_eq (by fun_prop) continuous_const)
  have hne : (confirmingEffects C u p).Nonempty :=
    ⟨u.toContinuousLinearMap, unit_proper hs, (pure_mem p).2⟩
  obtain ⟨f, hf, he⟩ := hF.exists_sInf_image_eq hne
    (show ContinuousOn (fun f : V →L[ℝ] ℝ => f x) _ from (by fun_prop).continuousOn)
  refine ⟨f, hf, ?_⟩
  rw [comparison, ← he]
  congr 1
  ext r
  constructor
  · rintro ⟨g, hg, hgr⟩
    exact ⟨g.toContinuousLinearMap, ⟨hg.1, hg.2⟩, hgr⟩
  · rintro ⟨g, hg, hgr⟩
    exact ⟨g.toLinearMap, ⟨hg.1, hg.2⟩, hgr⟩

/-- The original minimum definition agrees with existential exclusion on all of K. -/
theorem comparison_zero_iff
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (p : pure C u)
    {x : V} (hx : x ∈ base C u) :
    comparison C u p x = 0 ↔ x ∈ exclusion C u p := by
  obtain ⟨f, hf, he⟩ := comparison_attained hs hg p x
  constructor
  · intro hz
    exact ⟨hx, f.toLinearMap, ⟨hf.1, hf.2⟩, he.symm.trans hz⟩
  · rintro ⟨_, g, hg', hgz⟩
    have hb : BddBelow {r | ∃ f, confirms C u p f ∧ f x = r} :=
      ⟨0, fun r ⟨a, ha, har⟩ => har ▸ (ha.1 x hx.1).1⟩
    apply le_antisymm
    · exact (csInf_le hb ⟨g, hg', hgz⟩)
    · rw [he]
      exact (hf.1 x hx.1).1

private theorem oscillation_continuous {F : Set V} (hF : IsCompact F) :
    Continuous (oscillation F) :=
  (hF.continuous_sSup (show Continuous (fun t : (V →L[ℝ] ℝ) × V => t.1 t.2) by
    fun_prop)).sub (hF.continuous_sInf (by fun_prop))

/-- Both effect and endpoint extrema are attained on the whole compact set. -/
theorem width_attained
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    {F : Set V} (hF : IsCompact F) (hne : F.Nonempty) :
    ∃ f ∈ effects C u, ∃ y ∈ F, ∃ z ∈ F,
      width C u F = f y - f z ∧
      (∀ g ∈ effects C u, oscillation F g ≤ width C u F) ∧
      (∀ a ∈ F, f z ≤ f a ∧ f a ≤ f y) := by
  have hE := effects_compact hs hg
  have hEne : (effects C u).Nonempty := ⟨0, by intro x hx; simp [effects, proper, unit_proper hs x hx]⟩
  obtain ⟨f, hf, hw, hmax⟩ := hE.exists_sSup_image_eq_and_ge hEne
    (oscillation_continuous hF).continuousOn
  obtain ⟨y, hy, hsup, htop⟩ := hF.exists_sSup_image_eq_and_ge hne f.continuous.continuousOn
  obtain ⟨z, hz, hinf, hbot⟩ := hF.exists_sInf_image_eq_and_le hne f.continuous.continuousOn
  refine ⟨f, hf, y, hy, z, hz, ?_, ?_, ?_⟩
  · exact hw.trans (by rw [oscillation, hsup, hinf])
  · simpa only [width] using hmax
  · exact fun a ha => ⟨hbot a ha, htop a ha⟩

private theorem common_ball
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p q : pure C u) {y z : V} (hy : y ∈ exclusion C u p ∩ exclusion C u q)
    (hz : z ∈ exclusion C u p ∩ exclusion C u q) (hyz : y ≠ z) :
    exclusion C u p = exclusion C u q := by
  have all := (exclusion_ball_faces hc hs hg hB).1
  have hface := (all p).2.2.2.2.1.inter (all q).2.2.2.2.1
  have hconv := (all p).2.2.1.inter (all q).2.2.1
  have hn : (exclusion C u p ∩ exclusion C u q).Nontrivial := ⟨y, hy, z, hz, hyz⟩
  obtain ⟨bp⟩ := hB p
  obtain ⟨bq⟩ := hB q
  exact (chart_face_eq bp hconv
    (hface.mono (all p).2.2.2.2.1.subset inter_subset_left) hn).symm.trans
    (chart_face_eq bq hconv
      (hface.mono (all q).2.2.2.2.1.subset inter_subset_right) hn)

/-- Two distinct common zeros force a confirmed state to be pure when labels are faithful. -/
theorem common_zero_pure
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun p : pure C u => exclusion C u p))
    {x y z : V} (hx : x ∈ base C u) (hy : y ∈ base C u) (hz : z ∈ base C u)
    (hyz : y ≠ z) {e : V →L[ℝ] ℝ} (he : e ∈ effects C u)
    (hex : e x = 1) (hey : e y = 0) (hez : e z = 0) : x ∈ pure C u := by
  let H := e.toExposed (base C u)
  have hHexp : IsExposed ℝ (base C u) H := ContinuousLinearMap.toExposed.isExposed
  have hone (s : V) : s ∈ H ↔ s ∈ base C u ∧ e s = 1 := by
    constructor
    · rintro ⟨hsK, hm⟩
      exact ⟨hsK, le_antisymm (by simpa [hsK.2] using (he s hsK.1).2)
        (by simpa [hex] using hm x hx)⟩
    · rintro ⟨hsK, hes⟩
      exact ⟨hsK, fun t ht => by simpa [hes, ht.2] using (he t ht.1).2⟩
  have hxH : x ∈ H := (hone x).mpr ⟨hx, hex⟩
  have hHc := hHexp.isCompact (base_compact hc hs)
  obtain ⟨p, hp⟩ := hHc.extremePoints_nonempty ⟨x, hxH⟩
  have hpP : p ∈ pure C u := hHexp.isExtreme.extremePoints_subset_extremePoints hp
  have hsub : H.extremePoints ℝ ⊆ {p} := by
    intro q hq
    have hqP : q ∈ pure C u := hHexp.isExtreme.extremePoints_subset_extremePoints hq
    have hpE : confirms C u p e.toLinearMap := ⟨he, ((hone p).mp hp.1).2⟩
    have hqE : confirms C u q e.toLinearMap := ⟨he, ((hone q).mp hq.1).2⟩
    have heq := common_ball hc hs hg hB ⟨q, hqP⟩ ⟨p, hpP⟩
      ⟨⟨hy, e.toLinearMap, hqE, hey⟩, hy, e.toLinearMap, hpE, hey⟩
      ⟨⟨hz, e.toLinearMap, hqE, hez⟩, hz, e.toLinearMap, hpE, hez⟩ hyz
    exact congrArg Subtype.val (hInj heq)
  have hHull : H ⊆ {p} := by
    rw [← closure_convexHull_extremePoints hHc (hHexp.convex (base_convex C u))]
    exact closure_minimal (convexHull_min hsub (convex_singleton p)) isClosed_singleton
  have hxp : x = p := hHull hxH
  exact hxp ▸ hpP

end D5.S3.Quantum.Foundation.ExclusionWidthCompactness
