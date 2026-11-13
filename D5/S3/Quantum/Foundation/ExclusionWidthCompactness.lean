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

/-! Original full-effect oscillations and common-zero endpoint certificates. -/

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

omit [FiniteDimensional ℝ V] in
private theorem unit_proper (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) : proper C u u := by
  intro x hx
  refine ⟨?_, le_rfl⟩
  by_cases hz : x = 0
  · simp [hz]
  · exact (hs x hx hz).le

/-- The minimum over every original confirmer is attained, also at mixed inputs. -/
private theorem comparison_attained
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (p : pure C u) (x : V) :
    ∃ f : V →L[ℝ] ℝ, f ∈ confirmingEffects C u p ∧ comparison C u p x = f x := by
  have hF : IsCompact (confirmingEffects C u p) :=
    (effects_compact hs hg).inter_right (isClosed_eq (by fun_prop) continuous_const)
  have hne : (confirmingEffects C u p).Nonempty :=
    ⟨u.toContinuousLinearMap, unit_proper hs, (pure_mem p).2⟩
  obtain ⟨f, hf, he⟩ := hF.exists_sInf_image_eq hne
    (show Continuous (fun f : V →L[ℝ] ℝ => f x) from by fun_prop).continuousOn
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
private theorem comparison_zero_iff
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

omit [FiniteDimensional ℝ V] in
private theorem oscillation_continuous {F : Set V} (hF : IsCompact F) :
    Continuous (oscillation F) :=
  (hF.continuous_sSup (show Continuous (fun t : (V →L[ℝ] ℝ) × V => t.1 t.2) by
    fun_prop)).sub (hF.continuous_sInf (by fun_prop))

/-- Both effect and endpoint extrema are attained on the whole compact set. -/
private theorem width_attained
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    {F : Set V} (hF : IsCompact F) (hne : F.Nonempty) :
    ∃ f ∈ effects C u, ∃ y ∈ F, ∃ z ∈ F,
      width C u F = f y - f z ∧
      (∀ g ∈ effects C u, oscillation F g ≤ width C u F) ∧
      (∀ a ∈ F, f z ≤ f a ∧ f a ≤ f y) := by
  have hE := effects_compact hs hg
  have hEne : (effects C u).Nonempty := ⟨0, by
    intro x hx
    exact ⟨by simp, by simpa using (unit_proper hs x hx).1⟩⟩
  obtain ⟨f, hf, hw, hmax⟩ := hE.exists_sSup_image_eq_and_ge hEne
    (oscillation_continuous hF).continuousOn
  obtain ⟨y, hy, hsup, htop⟩ := hF.exists_sSup_image_eq_and_ge hne f.continuous.continuousOn
  obtain ⟨z, hz, hinf, hbot⟩ := hF.exists_sInf_image_eq_and_le hne f.continuous.continuousOn
  refine ⟨f, hf, y, hy, z, hz, ?_, ?_, ?_⟩
  · exact hw.trans (by rw [oscillation, hsup, hinf])
  · intro g hg'
    exact (hmax g hg').trans_eq hw.symm
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

private theorem common_zero_pure_of_unique
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    {x y z : V} (hx : x ∈ base C u) (hy : y ∈ base C u) (hz : z ∈ base C u)
    (hyz : y ≠ z) {e : V →L[ℝ] ℝ} (he : e ∈ effects C u)
    (hex : e x = 1) (hey : e y = 0) (hez : e z = 0)
    (hUnique : ∀ p q : pure C u, e p = 1 → e q = 1 →
      exclusion C u p = exclusion C u q → p = q) : x ∈ pure C u := by
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
    exact congrArg Subtype.val (hUnique ⟨q, hqP⟩ ⟨p, hpP⟩ hqE.2 hpE.2 heq)
  have hHull : H ⊆ {p} := by
    rw [← closure_convexHull_extremePoints hHc (hHexp.convex (base_convex C u))]
    exact closure_minimal (convexHull_min hsub (convex_singleton p)) isClosed_singleton
  have hxp : x = p := hHull hxH
  exact hxp ▸ hpP

/-- Two distinct common zeros force a confirmed state to be pure when labels are faithful. -/
private theorem common_zero_pure
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun p : pure C u => exclusion C u p))
    {x y z : V} (hx : x ∈ base C u) (hy : y ∈ base C u) (hz : z ∈ base C u)
    (hyz : y ≠ z) {e : V →L[ℝ] ℝ} (he : e ∈ effects C u)
    (hex : e x = 1) (hey : e y = 0) (hez : e z = 0) : x ∈ pure C u :=
  common_zero_pure_of_unique hc hs hg hB hx hy hz hyz he hex hey hez
    (fun _ _ _ _ heq => hInj heq)

private theorem effect_difference_le_width
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    {F : Set V} (hF : IsCompact F) {f : V →L[ℝ] ℝ} (hf : f ∈ effects C u)
    {y z : V} (hy : y ∈ F) (hz : z ∈ F) : f y - f z ≤ width C u F := by
  obtain ⟨_, _, _, _, _, _, _, hm, _⟩ := width_attained hs hg hF ⟨y, hy⟩
  have hu := le_csSup (hF.bddAbove_image f.continuous.continuousOn) (mem_image_of_mem f hy)
  have hl := csInf_le (hF.bddBelow_image f.continuous.continuousOn) (mem_image_of_mem f hz)
  exact (sub_le_sub hu hl).trans (hm f hf)

private theorem width_bounds
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    {F : Set V} (hF : IsCompact F) (hne : F.Nonempty) (hsub : F ⊆ base C u) :
    0 ≤ width C u F ∧ width C u F ≤ 1 := by
  obtain ⟨f, hf, y, hy, z, hz, hw, _, horder⟩ := width_attained hs hg hF hne
  rw [hw]
  refine ⟨sub_nonneg.mpr (horder y hy).1, ?_⟩
  have hfy := (hf y (hsub hy).1).2
  have hfz := (hf z (hsub hz).1).1
  rw [(hsub hy).2] at hfy
  change f y ≤ 1 at hfy
  change 0 ≤ f z at hfz
  linarith

private theorem effects_separate
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    {y z : V} (hy : y ∈ base C u) (hz : z ∈ base C u) (hyz : y ≠ z) :
    ∃ f ∈ effects C u, f y ≠ f z := by
  obtain ⟨l, hl⟩ := SeparatingDual.exists_separating_of_ne (R := ℝ) hyz
  have hK := base_compact hc hs
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn ⟨y, hy⟩ l.continuous.continuousOn
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn ⟨y, hy⟩ l.continuous.continuousOn
  have hab : l a < l b := by
    have hay : l a ≤ l y := hmin hy
    have haz : l a ≤ l z := hmin hz
    have hyb : l y ≤ l b := hmax hy
    have hzb : l z ≤ l b := hmax hz
    exact lt_of_le_of_ne (hay.trans hyb) (by intro he; apply hl; linarith)
  let f : V →L[ℝ] ℝ := (l b - l a)⁻¹ • (l - l a • u.toContinuousLinearMap)
  have hproper : f ∈ effects C u := by
    apply cone_bound hK hs
    intro p
    have hp := pure_mem p
    have hlo := hmin hp
    have hhi := hmax hp
    change 0 ≤ (l b - l a)⁻¹ * (l p - l a * u p) ∧
      (l b - l a)⁻¹ * (l p - l a * u p) ≤ 1
    rw [hp.2, mul_one]
    constructor
    · exact mul_nonneg (inv_nonneg.mpr (sub_pos.mpr hab).le) (sub_nonneg.mpr hlo)
    · rw [inv_mul_eq_div]
      exact (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right hhi _)
  refine ⟨f, hproper, ?_⟩
  intro he
  apply hl
  change (l b - l a)⁻¹ * (l y - l a * u y) =
    (l b - l a)⁻¹ * (l z - l a * u z) at he
  simp only [hy.2, hz.2, mul_one] at he
  have hh : l y - l a = l z - l a :=
    mul_left_cancel₀ (inv_ne_zero (ne_of_gt (sub_pos.mpr hab))) he
  linarith

/-- Every entire positive-dimensional original exclusion ball has positive width at most one. -/
private theorem exclusion_width_pos_le_one
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) : 0 < width C u (exclusion C u p) ∧ width C u (exclusion C u p) ≤ 1 := by
  have g := (exclusion_ball_faces hc hs hg hB).1 p
  obtain ⟨y, hy, z, hz, hyz⟩ := g.1
  obtain ⟨f, hf, hsep⟩ := effects_separate hc hs hy.1 hz.1 hyz
  have hle := effect_difference_le_width hs hg g.2.1 hf hy hz
  have hle' := effect_difference_le_width hs hg g.2.1 hf hz hy
  have hb := width_bounds hs hg g.2.1 g.1.nonempty (fun _ h => h.1)
  refine ⟨?_, hb.2⟩
  rcases lt_or_gt_of_ne hsep with h | h <;> linarith

private theorem saturated_endpoint_pure
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) {b : V →L[ℝ] ℝ} (hb : b ∈ effects C u)
    {y z : V} (hy : y ∈ exclusion C u p) (hz : z ∈ exclusion C u p)
    (hby : b y = 1) (hbz : b z = 0) : y ∈ pure C u := by
  have g := (exclusion_ball_faces hc hs hg hB).1 p
  let H := b.toExposed (base C u)
  have hH : IsExposed ℝ (base C u) H := ContinuousLinearMap.toExposed.isExposed
  have hone (s : V) : s ∈ H ↔ s ∈ base C u ∧ b s = 1 := by
    constructor
    · rintro ⟨hsK, hm⟩
      refine ⟨hsK, le_antisymm (by simpa [hsK.2] using (hb s hsK.1).2) ?_⟩
      simpa [hby] using hm y hy.1
    · rintro ⟨hsK, hbs⟩
      exact ⟨hsK, fun t ht => by simpa [hbs, ht.2] using (hb t ht.1).2⟩
  have hyH : y ∈ exclusion C u p ∩ H := ⟨hy, (hone y).mpr ⟨hy.1, hby⟩⟩
  have hface := g.2.2.2.2.1.inter hH.isExtreme
  have hsing : (exclusion C u p ∩ H).Subsingleton := by
    apply Set.not_nontrivial_iff.mp
    intro hn
    obtain ⟨chart⟩ := hB p
    have heq := chart_face_eq chart (g.2.2.1.inter (hH.convex (base_convex C u)))
      (hface.mono g.2.2.2.2.1.subset inter_subset_left) hn
    have hzH : z ∈ H := (heq.symm ▸ hz).2
    have := ((hone z).mp hzH).2
    linarith
  have hEq := hsing.eq_singleton_of_mem hyH
  apply isExtreme_singleton.mp
  rw [← hEq]
  exact hface

/-- A full original effect reaching both zero and one on a ball forces its label to be unique.
No global injectivity is used. -/
private theorem saturated_label_unique
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p q : pure C u) (hpq : exclusion C u p = exclusion C u q)
    {b : V →L[ℝ] ℝ} (hb : b ∈ effects C u)
    {y z : V} (hy : y ∈ exclusion C u p) (hz : z ∈ exclusion C u p)
    (hby : b y = 1) (hbz : b z = 0) : p = q := by
  by_contra hpne
  have hcomp : u.toContinuousLinearMap - b ∈ effects C u := by
    intro x hx
    change 0 ≤ u x - b x ∧ u x - b x ≤ u x
    exact ⟨sub_nonneg.mpr (hb x hx).2, sub_le_self _ (hb x hx).1⟩
  have hyP := saturated_endpoint_pure hc hs hg hB p hb hy hz hby hbz
  have hzP := saturated_endpoint_pure hc hs hg hB p hcomp hz hy
    (by change u z - b z = 1; rw [hz.1.2, hbz]; norm_num)
    (by change u y - b y = 0; rw [hy.1.2, hby]; norm_num)
  let y' : pure C u := ⟨y, hyP⟩
  let z' : pure C u := ⟨z, hzP⟩
  have hpY := (exclusion_symmetric p y').mp hy
  have hqY := (exclusion_symmetric q y').mp (hpq ▸ hy)
  have hpZ := (exclusion_symmetric p z').mp hz
  have hqZ := (exclusion_symmetric q z').mp (hpq ▸ hz)
  have heq := common_ball hc hs hg hB y' z' ⟨hpY, hpZ⟩ ⟨hqY, hqZ⟩
    (fun he => hpne (Subtype.ext he))
  have hyZ : y ∈ exclusion C u z' :=
    ⟨hy.1, (u.toContinuousLinearMap - b).toLinearMap,
      ⟨hcomp, by change u z - b z = 1; rw [hz.1.2, hbz]; norm_num⟩,
      by change u y - b y = 0; rw [hy.1.2, hby]; norm_num⟩
  have hyY : y ∈ exclusion C u y' := heq.symm ▸ hyZ
  obtain ⟨_, f, hf, hfy⟩ := hyY
  have := hf.2
  change f y = 1 at this
  linarith

private theorem saturated_common_zero_pure
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    {x y z : V} (hx : x ∈ base C u) (hy : y ∈ base C u) (hz : z ∈ base C u)
    {e b : V →L[ℝ] ℝ} (he : e ∈ effects C u) (hb : b ∈ effects C u)
    (hex : e x = 1) (hey : e y = 0) (hez : e z = 0)
    (hby : b y = 1) (hbz : b z = 0) : x ∈ pure C u := by
  have hyz : y ≠ z := by intro h; rw [h, hbz] at hby; norm_num at hby
  apply common_zero_pure_of_unique hc hs hg hB hx hy hz hyz he hex hey hez
  intro p q hep heq hpq
  exact saturated_label_unique hc hs hg hB p q hpq hb
    ⟨hy, e.toLinearMap, ⟨he, hep⟩, hey⟩
    ⟨hz, e.toLinearMap, ⟨he, hep⟩, hez⟩ hby hbz

/-- Joint original data: label, two endpoints, width effect and whole-zero confirmer. -/
abbrev EndpointData (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  V × V × V × (V →L[ℝ] ℝ) × (V →L[ℝ] ℝ)

/-- Closed certificates over the full state and effect domains; no purity is imposed. -/
def endpointCertificates (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (a : ℝ) :
    Set (EndpointData V) :=
  {t | t ∈ base C u ×ˢ base C u ×ˢ base C u ×ˢ effects C u ×ˢ effects C u ∧
    t.2.2.2.2 t.1 = 1 ∧ t.2.2.2.2 t.2.1 = 0 ∧ t.2.2.2.2 t.2.2.1 = 0 ∧
    a ≤ t.2.2.2.1 t.2.1 - t.2.2.2.1 t.2.2.1}

private theorem certificates_compact
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (a : ℝ) :
    IsCompact (endpointCertificates C u a) := by
  have hK := base_compact hc hs
  have hE := effects_compact hs hg
  have h1 : IsClosed {t : EndpointData V | t.2.2.2.2 t.1 = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have h2 : IsClosed {t : EndpointData V | t.2.2.2.2 t.2.1 = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have h3 : IsClosed {t : EndpointData V | t.2.2.2.2 t.2.2.1 = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have h4 : IsClosed {t : EndpointData V |
      a ≤ t.2.2.2.1 t.2.1 - t.2.2.2.1 t.2.2.1} :=
    isClosed_le continuous_const (by fun_prop)
  have hcond : IsClosed {t : EndpointData V |
      t.2.2.2.2 t.1 = 1 ∧ t.2.2.2.2 t.2.1 = 0 ∧ t.2.2.2.2 t.2.2.1 = 0 ∧
      a ≤ t.2.2.2.1 t.2.1 - t.2.2.2.1 t.2.2.1} :=
    h1.inter (h2.inter (h3.inter h4))
  exact (hK.prod (hK.prod (hK.prod (hE.prod hE)))).inter_right hcond

private theorem certificate_iff_width
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (a : ℝ) :
    (p : V) ∈ Prod.fst '' endpointCertificates C u a ↔
      a ≤ width C u (exclusion C u p) := by
  constructor
  · rintro ⟨t, ht, htp⟩
    have he : confirms C u p t.2.2.2.2.toLinearMap :=
      ⟨ht.1.2.2.2.2, htp ▸ ht.2.1⟩
    exact ht.2.2.2.2.trans (effect_difference_le_width hs hg
      ((exclusion_ball_faces hc hs hg hB).1 p).2.1 ht.1.2.2.2.1
      ⟨ht.1.2.1, t.2.2.2.2.toLinearMap, he, ht.2.2.1⟩
      ⟨ht.1.2.2.1, t.2.2.2.2.toLinearMap, he, ht.2.2.2.1⟩)
  · intro ha
    have g := (exclusion_ball_faces hc hs hg hB).1 p
    obtain ⟨b, hb, y, hy, z, hz, hw, _, _⟩ := width_attained hs hg g.2.1 g.1.nonempty
    obtain ⟨e, he, hzero⟩ := g.2.2.2.2.2.2
    have hey : e y = 0 := (hzero ▸ hy).2
    have hez : e z = 0 := (hzero ▸ hz).2
    exact ⟨(p, y, z, b, e.toContinuousLinearMap),
      ⟨⟨pure_mem p, hy.1, hz.1, hb, he.1⟩, he.2, hey, hez, hw ▸ ha⟩, rfl⟩

private theorem attaining_certificate
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) : ∃ t ∈ endpointCertificates C u 0,
      t.1 = p ∧ t.2.2.2.1 t.2.1 - t.2.2.2.1 t.2.2.1 = width C u (exclusion C u p) := by
  have g := (exclusion_ball_faces hc hs hg hB).1 p
  obtain ⟨b, hb, y, hy, z, hz, hw, _, _⟩ := width_attained hs hg g.2.1 g.1.nonempty
  obtain ⟨e, he, hzero⟩ := g.2.2.2.2.2.2
  exact ⟨(p, y, z, b, e.toContinuousLinearMap),
    ⟨⟨pure_mem p, hy.1, hz.1, hb, he.1⟩, he.2, (hzero ▸ hy).2, (hzero ▸ hz).2,
      hw ▸ (exclusion_width_pos_le_one hc hs hg hB p).1.le⟩, rfl, hw.symm⟩

/-- Width on the relative pure carrier is upper semicontinuous under EB alone. -/
theorem width_upperSemicontinuous
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u) :
    UpperSemicontinuous (fun p : pure C u => width C u (exclusion C u p)) := by
  apply upperSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  have heq : (fun p : pure C u => width C u (exclusion C u p)) ⁻¹' Ici a =
      Subtype.val ⁻¹' (Prod.fst '' endpointCertificates C u a) := by
    ext p
    exact (certificate_iff_width hc hs hg hB p a).symm
  rw [heq]
  exact ((certificates_compact hc hs hg a).image continuous_fst).isClosed.preimage
    continuous_subtype_val

/-- Positive width layers are compact in the ambient original base, including the empty case. -/
theorem positive_width_layer_compact
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun p : pure C u => exclusion C u p))
    {a : ℝ} (ha : 0 < a) :
    IsCompact {x | x ∈ pure C u ∧ a ≤ width C u (exclusion C u x)} := by
  have heq : {x | x ∈ pure C u ∧ a ≤ width C u (exclusion C u x)} =
      Prod.fst '' endpointCertificates C u a := by
    ext x
    constructor
    · rintro ⟨hp, hw⟩
      exact (certificate_iff_width hc hs hg hB ⟨x, hp⟩ a).mpr hw
    · rintro ⟨t, ht, rfl⟩
      have hne : t.2.1 ≠ t.2.2.1 := by
        intro he
        have hh := ht.2.2.2.2
        rw [he, sub_self] at hh
        exact (not_le_of_gt ha) hh
      have hp := common_zero_pure hc hs hg hB hInj ht.1.1 ht.1.2.1 ht.1.2.2.1
        hne ht.1.2.2.2.2 ht.2.1 ht.2.2.1 ht.2.2.2.1
      exact ⟨hp, (certificate_iff_width hc hs hg hB ⟨t.1, hp⟩ a).mp ⟨t, ht, rfl⟩⟩
  rw [heq]
  exact (certificates_compact hc hs hg a).image continuous_fst

/-- The full minimum-defined original exclusions have the same attained positive width. -/
theorem original_exclusion_width
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) :
    let F := {x | x ∈ base C u ∧ comparison C u p x = 0}
    (0 < width C u F ∧ width C u F ≤ 1) ∧
    ∃ f ∈ effects C u, ∃ y ∈ F, ∃ z ∈ F, width C u F = f y - f z := by
  have hF : {x | x ∈ base C u ∧ comparison C u p x = 0} = exclusion C u p := by
    ext x
    constructor
    · rintro ⟨hx, hz⟩
      exact (comparison_zero_iff hs hg p hx).mp hz
    · intro hx
      exact ⟨hx.1, (comparison_zero_iff hs hg p hx.1).mpr hx⟩
  dsimp only
  rw [hF]
  refine ⟨exclusion_width_pos_le_one hc hs hg hB p, ?_⟩
  have g := (exclusion_ball_faces hc hs hg hB).1 p
  obtain ⟨f, hf, y, hy, z, hz, hw, _, _⟩ := width_attained hs hg g.2.1 g.1.nonempty
  exact ⟨f, hf, y, hy, z, hz, hw⟩

omit [FiniteDimensional ℝ V] in
private theorem certificate_saturated {t : EndpointData V}
    (ht : t ∈ endpointCertificates C u 1) :
    t.2.2.2.1 t.2.1 = 1 ∧ t.2.2.2.1 t.2.2.1 = 0 := by
  have htop : t.2.2.2.1 t.2.1 ≤ 1 := by
    simpa [ht.1.2.1.2] using (ht.1.2.2.2.1 t.2.1 ht.1.2.1.1).2
  have hbot : 0 ≤ t.2.2.2.1 t.2.2.1 := (ht.1.2.2.2.1 t.2.2.1 ht.1.2.2.1.1).1
  have hdiff := ht.2.2.2.2
  constructor <;> linarith

/-- Saturated labels form an ambient compact set under EB alone. -/
theorem saturated_labels_compact
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u) :
    IsCompact {x | x ∈ pure C u ∧ width C u (exclusion C u x) = 1} := by
  have heq : {x | x ∈ pure C u ∧ width C u (exclusion C u x) = 1} =
      Prod.fst '' endpointCertificates C u 1 := by
    ext x
    constructor
    · rintro ⟨hp, hw⟩
      exact (certificate_iff_width hc hs hg hB ⟨x, hp⟩ 1).mpr hw.ge
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨hby, hbz⟩ := certificate_saturated ht
      have hp := saturated_common_zero_pure hc hs hg hB ht.1.1 ht.1.2.1 ht.1.2.2.1
        ht.1.2.2.2.2 ht.1.2.2.2.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 hby hbz
      exact ⟨hp, le_antisymm (exclusion_width_pos_le_one hc hs hg hB ⟨t.1, hp⟩).2
        ((certificate_iff_width hc hs hg hB ⟨t.1, hp⟩ 1).mp ⟨t, ht, rfl⟩)⟩
  rw [heq]
  exact (certificates_compact hc hs hg 1).image continuous_fst

/-- At a mixed ambient limit, widths tend to zero under faithful labeling. -/
theorem width_tendsto_zero_of_mixed_limit
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun p : pure C u => exclusion C u p))
    (p : ℕ → pure C u) {x : V}
    (hpx : Tendsto (fun n => (p n : V)) atTop (𝓝 x)) (hx : x ∉ pure C u) :
    Tendsto (fun n => width C u (exclusion C u (p n))) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans (exclusion_width_pos_le_one hc hs hg hB (p n)).1
  · intro a ha
    have hL := positive_width_layer_compact hc hs hg hB hInj ha
    have hnot : x ∈ {x | x ∈ pure C u ∧ a ≤ width C u (exclusion C u x)}ᶜ :=
      fun h => hx h.1
    have hev := hpx.eventually_mem (hL.isClosed.isOpen_compl.mem_nhds hnot)
    filter_upwards [hev] with n hn
    exact lt_of_not_ge (fun h => hn ⟨(p n).property, h⟩)

private theorem far_labels_compact
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (a : ℝ) :
    IsCompact (Prod.fst '' {t ∈ endpointCertificates C u 0 | a ≤ dist t.2.1 t.2.2.1}) := by
  have hd : IsClosed {t : EndpointData V | a ≤ dist t.2.1 t.2.2.1} :=
    isClosed_le continuous_const (by fun_prop)
  exact ((certificates_compact hc hs hg 0).inter_right hd).image continuous_fst

/-- Entire ball diameters collapse at a mixed label limit, independently of width estimates. -/
theorem diameter_tendsto_zero_of_mixed_limit
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun p : pure C u => exclusion C u p))
    (p : ℕ → pure C u) {x : V}
    (hpx : Tendsto (fun n => (p n : V)) atTop (𝓝 x)) (hx : x ∉ pure C u) :
    Tendsto (fun n => Metric.diam (exclusion C u (p n))) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le Metric.diam_nonneg
  · intro a ha
    let δ := a / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    let L := Prod.fst '' {t ∈ endpointCertificates C u 0 | δ ≤ dist t.2.1 t.2.2.1}
    have hL : IsCompact L := far_labels_compact hc hs hg δ
    have hnot : x ∈ Lᶜ := by
      rintro ⟨t, ⟨ht, hdist⟩, rfl⟩
      apply hx
      have hne : t.2.1 ≠ t.2.2.1 := by
        intro heq
        simpa [heq] using hδ.trans_le hdist
      exact common_zero_pure hc hs hg hB hInj ht.1.1 ht.1.2.1 ht.1.2.2.1 hne
        ht.1.2.2.2.2 ht.2.1 ht.2.2.1 ht.2.2.2.1
    have hev := hpx.eventually_mem (hL.isClosed.isOpen_compl.mem_nhds hnot)
    filter_upwards [hev] with n hn
    have hd : Metric.diam (exclusion C u (p n)) ≤ δ := by
      apply Metric.diam_le_of_forall_dist_le hδ.le
      intro y hy z hz
      apply le_of_lt
      apply lt_of_not_ge
      intro hdist
      apply hn
      have g := (exclusion_ball_faces hc hs hg hB).1 (p n)
      obtain ⟨e, he, hzero⟩ := g.2.2.2.2.2.2
      have h0 : (0 : V →L[ℝ] ℝ) ∈ effects C u := by
        intro v hv
        exact ⟨by simp, by simpa using (unit_proper hs v hv).1⟩
      exact ⟨((p n : V), y, z, 0, e.toContinuousLinearMap),
        ⟨⟨⟨pure_mem (p n), hy.1, hz.1, h0, he.1⟩,
          he.2, (hzero ▸ hy).2, (hzero ▸ hz).2, by simp⟩, hdist⟩, rfl⟩
    exact hd.trans_lt (by dsimp [δ]; linarith)

/-- The positive reciprocal-integer layers exhaust all original pure states. -/
theorem pure_eq_countable_width_layers
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u) :
    pure C u = ⋃ n : ℕ, {x | x ∈ pure C u ∧
      1 / (n + 1 : ℝ) ≤ width C u (exclusion C u x)} := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt
      (exclusion_width_pos_le_one hc hs hg hB ⟨x, hx⟩).1
    exact mem_iUnion.mpr ⟨n, hx, hn.le⟩
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact hn.1

/-- The positive global supremum is attained at an actual original pure label. -/
theorem width_global_maximum [Nontrivial V]
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun p : pure C u => exclusion C u p)) :
    ∃ p : pure C u, 0 < width C u (exclusion C u p) ∧
      width C u (exclusion C u p) ≤ 1 ∧
      (∀ q : pure C u, width C u (exclusion C u q) ≤ width C u (exclusion C u p)) ∧
      sSup ((fun q : pure C u => width C u (exclusion C u q)) '' univ) =
        width C u (exclusion C u p) := by
  have original_bounds (r : pure C u) :
      0 < width C u (exclusion C u r) ∧ width C u (exclusion C u r) ≤ 1 := by
    have hF : {x | x ∈ base C u ∧ comparison C u r x = 0} = exclusion C u r := by
      ext x
      constructor
      · rintro ⟨hx, hz⟩
        exact (comparison_zero_iff hs hg r hx).mp hz
      · intro hx
        exact ⟨hx.1, (comparison_zero_iff hs hg r hx.1).mpr hx⟩
    simpa only [hF] using (original_exclusion_width hc hs hg hB r).1
  obtain ⟨q⟩ := OriginalFacePolarity.pure_nonempty hc hs hg
  have hq := (Set.ext_iff.mp (pure_eq_countable_width_layers hc hs hg hB) (q : V)).mp
    q.property
  obtain ⟨n, _, hqn⟩ := mem_iUnion.mp hq
  let a : ℝ := 1 / (n + 1 : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  let L : Set (pure C u) := {p | a ≤ width C u (exclusion C u p)}
  have hL : IsCompact L := by
    apply Subtype.isCompact_iff.mpr
    have him : Subtype.val '' L = {x | x ∈ pure C u ∧ a ≤ width C u (exclusion C u x)} := by
      ext x
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.property, hp⟩
      · rintro ⟨hp, hw⟩
        exact ⟨⟨x, hp⟩, hw, rfl⟩
    rw [him]
    exact positive_width_layer_compact hc hs hg hB hInj ha
  obtain ⟨p, hp, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
    (show L.Nonempty from ⟨q, hqn⟩) hL
    ((width_upperSemicontinuous hc hs hg hB).upperSemicontinuousOn L)
  have hall (r : pure C u) : width C u (exclusion C u r) ≤ width C u (exclusion C u p) := by
    by_cases hr : a ≤ width C u (exclusion C u r)
    · exact hmax hr
    · exact (le_of_lt (lt_of_not_ge hr)).trans hp
  refine ⟨p, (original_bounds p).1, (original_bounds p).2, hall, ?_⟩
  apply le_antisymm
  · exact csSup_le (by exact ⟨_, p, mem_univ p, rfl⟩) (by rintro _ ⟨r, _, rfl⟩; exact hall r)
  · exact le_csSup ⟨1, by rintro _ ⟨r, _, rfl⟩; exact (original_bounds r).2⟩
      ⟨p, mem_univ p, rfl⟩

/-- Every near-saturated sequence has a strictly indexed subsequence converging to saturation. -/
theorem near_saturation_subsequence
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : ℕ → pure C u)
    (hw : Tendsto (fun n => width C u (exclusion C u (p n))) atTop (𝓝 1)) :
    ∃ q : pure C u, width C u (exclusion C u q) = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => (p (φ n) : V)) atTop (𝓝 (q : V)) := by
  choose T hT hTp hTw using fun n => attaining_certificate hc hs hg hB (p n)
  obtain ⟨t, ht, φ, hφ, hlim⟩ := (certificates_compact hc hs hg 0).tendsto_subseq hT
  have hd : t.2.2.2.1 t.2.1 - t.2.2.2.1 t.2.2.1 = 1 := by
    apply tendsto_nhds_unique
      (((show Continuous (fun t : EndpointData V =>
        t.2.2.2.1 t.2.1 - t.2.2.2.1 t.2.2.1) by fun_prop).tendsto t).comp hlim)
    exact (hw.comp hφ.tendsto_atTop).congr'
      (Eventually.of_forall fun n => (hTw (φ n)).symm)
  have ht1 : t ∈ endpointCertificates C u 1 :=
    ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, hd.ge⟩
  obtain ⟨hby, hbz⟩ := certificate_saturated ht1
  have hp := saturated_common_zero_pure hc hs hg hB ht.1.1 ht.1.2.1 ht.1.2.2.1
    ht.1.2.2.2.2 ht.1.2.2.2.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 hby hbz
  refine ⟨⟨t.1, hp⟩, le_antisymm (exclusion_width_pos_le_one hc hs hg hB ⟨t.1, hp⟩).2
    ((certificate_iff_width hc hs hg hB ⟨t.1, hp⟩ 1).mp ⟨t, ht1, rfl⟩), φ, hφ, ?_⟩
  have hfirst := continuous_fst.tendsto t |>.comp hlim
  exact hfirst.congr' (Eventually.of_forall fun n => hTp (φ n))

/-- Absence of saturation forces a uniform strict upper gap under EB alone. -/
theorem no_saturation_uniform_gap
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hno : ∀ p : pure C u, width C u (exclusion C u p) ≠ 1) :
    sSup ((fun p : pure C u => width C u (exclusion C u p)) '' univ) < 1 := by
  by_cases hP : Nonempty (pure C u)
  · obtain ⟨p⟩ := hP
    obtain ⟨t0, ht0, _, _⟩ := attaining_certificate hc hs hg hB p
    let d : EndpointData V → ℝ := fun t => t.2.2.2.1 t.2.1 - t.2.2.2.1 t.2.2.1
    obtain ⟨t, ht, hmax⟩ := (certificates_compact hc hs hg 0).exists_isMaxOn
      ⟨t0, ht0⟩ (show Continuous d from by dsimp [d]; fun_prop).continuousOn
    have htop : t.2.2.2.1 t.2.1 ≤ 1 := by
      simpa [ht.1.2.1.2] using (ht.1.2.2.2.1 t.2.1 ht.1.2.1.1).2
    have hbot : 0 ≤ t.2.2.2.1 t.2.2.1 := (ht.1.2.2.2.1 t.2.2.1 ht.1.2.2.1.1).1
    have hdle : d t ≤ 1 := by dsimp [d]; linarith
    have hdlt : d t < 1 := lt_of_le_of_ne hdle (by
      intro heq
      have ht1 : t ∈ endpointCertificates C u 1 :=
        ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, heq.ge⟩
      obtain ⟨hby, hbz⟩ := certificate_saturated ht1
      have hp := saturated_common_zero_pure hc hs hg hB ht.1.1 ht.1.2.1 ht.1.2.2.1
        ht.1.2.2.2.2 ht.1.2.2.2.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 hby hbz
      apply hno ⟨t.1, hp⟩
      exact le_antisymm (exclusion_width_pos_le_one hc hs hg hB ⟨t.1, hp⟩).2
        ((certificate_iff_width hc hs hg hB ⟨t.1, hp⟩ 1).mp ⟨t, ht1, rfl⟩))
    apply lt_of_le_of_lt _ hdlt
    apply csSup_le (by exact ⟨_, p, mem_univ p, rfl⟩)
    rintro _ ⟨q, _, rfl⟩
    obtain ⟨s, hs', _, hsw⟩ := attaining_certificate hc hs hg hB q
    calc
      width C u (exclusion C u q) = d s := hsw.symm
      _ ≤ d t := hmax hs'
  · have hem : ((fun p : pure C u => width C u (exclusion C u p)) '' univ) = ∅ := by
      ext x
      constructor
      · rintro ⟨p, _, _⟩
        exact (hP ⟨p⟩).elim
      · simp
    rw [hem, Real.sSup_empty]
    norm_num

end D5.S3.Quantum.Foundation.ExclusionWidthCompactness
