/- GID: D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Standard arcwise connected hereditary unicoherence and arc convexity. -/

import D5.S1.Dynamics.Shadowing.DendriteObstruction.CompactHistories

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
  have hφ : Continuous φ := A.continuous.continuous_restrict
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

end D5.S1.Dynamics.Shadowing.DendriteObstruction
