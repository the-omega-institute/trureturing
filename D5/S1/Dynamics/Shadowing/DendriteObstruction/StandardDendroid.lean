/- GID: D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Standard arcwise connected hereditary unicoherence and arc convexity. -/

import D5.S1.Dynamics.Shadowing.DendriteObstruction.CompactHistories

/-! Arc convexity from the standard static dendroid hypotheses. -/

open Set Function
open scoped Topology
open TopologicalSpace

namespace D5.S1.Dynamics.Shadowing.DendriteObstruction

variable {X : Type*} [MetricSpace X]

namespace EmbeddedArc

/-- A connected subset of an arc contains the interval between any two of its points. -/
theorem between_subset (A : EmbeddedArc X) {C : Set X} (hC : IsPreconnected C)
    (hCA : C ⊆ A.carrier) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hpa : A.param a ∈ C) (hpb : A.param b ∈ C) :
    A.param '' Icc a b ⊆ C := by
  let φ : Icc (0 : ℝ) 1 → X := fun u => A.param u
  have hφ : Continuous φ := continuousOn_iff_continuous_domRestrict.mp A.continuous
  have hi : Injective φ := fun u v h => Subtype.ext (A.injective u.2 v.2 h)
  have hr : C ⊆ range φ := by
    rintro x hx
    obtain ⟨u, hu, rfl⟩ := hCA hx
    exact ⟨⟨u, hu⟩, rfl⟩
  have hp := hC.preimage_of_isClosedMap hi hφ.isClosedMap hr
  have hreal := hp.image (fun u : Icc (0 : ℝ) 1 => (u : ℝ)) continuous_subtype_val.continuousOn
  have hinterval := hreal.Icc_subset
    (show a ∈ (fun u : Icc (0 : ℝ) 1 => (u : ℝ)) '' (φ ⁻¹' C) from ⟨⟨a, ha⟩, hpa, rfl⟩)
    (show b ∈ (fun u : Icc (0 : ℝ) 1 => (u : ℝ)) '' (φ ⁻¹' C) from ⟨⟨b, hb⟩, hpb, rfl⟩)
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨v, hv, he⟩ := hinterval hu
  change A.param (v : ℝ) ∈ C at hv
  simpa only [he] using hv

/-- Static hulls force every given arc between points of a continuum to lie in it. -/
theorem subset_continuum (A : EmbeddedArc X) (hull : StaticArcHull X) {C : Set X}
    (hc : IsCompact C) (hcon : IsConnected C)
    (h0 : A.param 0 ∈ C) (h1 : A.param 1 ∈ C) : A.carrier ⊆ C := by
  have hne : A.param 0 ≠ A.param 1 := by
    intro h
    have := A.injective (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      (by norm_num : (1 : ℝ) ∈ Icc 0 1) h
    norm_num at this
  obtain ⟨B, hB0, hB1, hB⟩ := hull _ _ hne
  have hBA : B.carrier ⊆ A.carrier := hB _ A.compact A.connected
    (mem_image_of_mem _ (by norm_num)) (mem_image_of_mem _ (by norm_num))
  have hAB : A.carrier ⊆ B.carrier := A.between_subset B.connected.isPreconnected hBA
    (by norm_num) (by norm_num)
    (hB0 ▸ mem_image_of_mem _ (by norm_num))
    (hB1 ▸ mem_image_of_mem _ (by norm_num))
  exact hAB.trans (hB _ hc hcon h0 h1)

end EmbeddedArc

/-- On a compact metric carrier, these are exactly arcwise connectedness and
hereditary unicoherence. No opening, packing or dynamical law is a field. -/
structure StandardDendroid (X : Type*) [MetricSpace X] : Prop where
  arcwise : ∀ p y : X, p ≠ y → ∃ A : EmbeddedArc X, A.param 0 = p ∧ A.param 1 = y
  unicoherent : ∀ C D : Set X, IsCompact C → IsConnected C →
    IsCompact D → IsConnected D → IsPreconnected (C ∩ D)

/-- Hereditary unicoherence makes the intersection with any arc order-convex. -/
theorem StandardDendroid.arc_convex (hX : StandardDendroid X) (A : EmbeddedArc X)
    {C : Set X} (hc : IsCompact C) (hcon : IsConnected C)
    (h0 : A.param 0 ∈ C) (h1 : A.param 1 ∈ C) : A.carrier ⊆ C := by
  have hpre := hX.unicoherent _ _ hc hcon A.compact A.connected
  have hh := A.between_subset hpre inter_subset_right (by norm_num) (by norm_num)
    ⟨h0, mem_image_of_mem _ (by norm_num)⟩ ⟨h1, mem_image_of_mem _ (by norm_num)⟩
  exact hh.trans inter_subset_left

/-- The accepted compact-history hull premise follows from the standard definition. -/
theorem StandardDendroid.staticArcHull (hX : StandardDendroid X) : StaticArcHull X := by
  intro p y hpy
  obtain ⟨A, h0, h1⟩ := hX.arcwise p y hpy
  refine ⟨A, h0, h1, fun C hc hcon hp hy => ?_⟩
  exact hX.arc_convex A hc hcon (h0 ▸ hp) (h1 ▸ hy)

/-- Any two arcs with the same ordered endpoints have the same carrier. -/
theorem StandardDendroid.arc_unique (hX : StandardDendroid X) (A B : EmbeddedArc X)
    (h0 : A.param 0 = B.param 0) (h1 : A.param 1 = B.param 1) : A.carrier = B.carrier := by
  apply Subset.antisymm
  · exact hX.arc_convex A B.compact B.connected
      (h0 ▸ mem_image_of_mem _ (by norm_num)) (h1 ▸ mem_image_of_mem _ (by norm_num))
  · exact hX.arc_convex B A.compact A.connected
      (h0.symm ▸ mem_image_of_mem _ (by norm_num))
      (h1.symm ▸ mem_image_of_mem _ (by norm_num))

/-- An embedded circle would give two distinct arcs with the same endpoints. -/
theorem StandardDendroid.no_circle (hX : StandardDendroid X)
    (g : AddCircle (1 : ℝ) → X) (hg : Continuous g) : ¬ Injective g := by
  intro hi
  let φ : ℝ → X := fun t => g (t : AddCircle (1 : ℝ))
  have hφ : Continuous φ := hg.comp (AddCircle.continuous_mk' 1)
  let A : EmbeddedArc X := {
    param := fun u => φ (u / 2)
    continuous := (hφ.comp (continuous_id.div_const 2)).continuousOn
    injective := by
      intro u hu v hv he
      have huv := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (0 : ℝ))
        (show u / 2 ∈ Ico 0 (0 + 1) from ⟨by linarith [hu.1], by linarith [hu.2]⟩)
        (show v / 2 ∈ Ico 0 (0 + 1) from ⟨by linarith [hv.1], by linarith [hv.2]⟩)).mp (hi he)
      linarith }
  let B : EmbeddedArc X := {
    param := fun u => φ (1 - u / 2)
    continuous := (hφ.comp (continuous_const.sub (continuous_id.div_const 2))).continuousOn
    injective := by
      intro u hu v hv he
      have huv := (AddCircle.coe_eq_coe_iff_of_mem_Ioc (p := (1 : ℝ)) (a := (0 : ℝ))
        (show 1 - u / 2 ∈ Ioc 0 (0 + 1) from ⟨by linarith [hu.2], by linarith [hu.1]⟩)
        (show 1 - v / 2 ∈ Ioc 0 (0 + 1) from ⟨by linarith [hv.2], by linarith [hv.1]⟩)).mp (hi he)
      linarith }
  have h10 : φ 1 = φ 0 := congrArg g (AddCircle.coe_period 1)
  have heq : A.carrier = B.carrier := hX.arc_unique A B
    (by simpa [A, B] using h10.symm) (by norm_num [A, B])
  have hmid : φ (1 / 4) ∈ B.carrier := by
    rw [← heq]
    exact ⟨1 / 2, by norm_num, by norm_num [A]⟩
  obtain ⟨u, hu, heu⟩ := hmid
  have ht : 1 - u / 2 ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  by_cases h1 : 1 - u / 2 = 1
  · have he : φ 0 = φ (1 / 4) := by simpa only [B, h1, h10] using heu
    have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (0 : ℝ))
      (by norm_num : (0 : ℝ) ∈ Ico 0 (0 + 1))
      (by norm_num : (1 / 4 : ℝ) ∈ Ico 0 (0 + 1))).mp (hi he)
    norm_num at hh
  · have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (0 : ℝ))
      (show 1 - u / 2 ∈ Ico 0 (0 + 1) from
        ⟨by linarith [ht.1], by simpa using lt_of_le_of_ne ht.2 h1⟩)
      (by norm_num : (1 / 4 : ℝ) ∈ Ico 0 (0 + 1))).mp (hi heu)
    linarith [ht.1]

/-- Every compact connected subset inherits the same standard dendroid geometry. -/
theorem StandardDendroid.subcontinuum (hX : StandardDendroid X) {C : Set X}
    (hc : IsCompact C) (hcon : IsConnected C) : StandardDendroid C := by
  constructor
  · intro p y hpy
    have hne : (p : X) ≠ (y : X) := fun h => hpy (Subtype.ext h)
    obtain ⟨A, h0, h1⟩ := hX.arcwise p y hne
    have hAC : A.carrier ⊆ C := hX.arc_convex A hc hcon (h0 ▸ p.2) (h1 ▸ y.2)
    let φ : Icc (0 : ℝ) 1 → C := fun u => ⟨A.param u, hAC (mem_image_of_mem _ u.2)⟩
    have hφ : Continuous φ := A.continuous.domRestrict.subtype_mk _
    let B : EmbeddedArc C := {
      param := IccExtend (by norm_num : (0 : ℝ) ≤ 1) φ
      continuous := hφ.Icc_extend'.continuousOn
      injective := by
        intro u hu v hv he
        simp only [IccExtend_of_mem (by norm_num : (0 : ℝ) ≤ 1) φ hu, IccExtend_of_mem (by norm_num : (0 : ℝ) ≤ 1) φ hv] at he
        exact A.injective hu hv (congrArg Subtype.val he) }
    refine ⟨B, ?_, ?_⟩
    · apply Subtype.ext
      simpa only [B, IccExtend_left] using h0
    · apply Subtype.ext
      simpa only [B, IccExtend_right] using h1
  · intro P Q hPc hPcon hQc hQcon
    apply (Topology.IsInducing.subtypeVal.isPreconnected_image).mp
    rw [image_inter Subtype.val_injective]
    exact hX.unicoherent _ _ (hPc.image continuous_subtype_val)
      (hPcon.image _ continuous_subtype_val.continuousOn)
      (hQc.image continuous_subtype_val) (hQcon.image _ continuous_subtype_val.continuousOn)

end D5.S1.Dynamics.Shadowing.DendriteObstruction
