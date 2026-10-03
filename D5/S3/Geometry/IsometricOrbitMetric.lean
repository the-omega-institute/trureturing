/- GID: D5/S3/Geometry/IsometricOrbitMetric
   generality: G
   mirror-B: D5/B/S3/Geometry/IsometricOrbitMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.MetricSpace.HausdorffDistance]
   utility: none
   digest: Compatible orbit metrics; proper ambient spaces give proper orbit quotients. -/

import D5.S3.Geometry.MostowPrasadCovering
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

open Set Metric Topology
open D5.S3.Geometry.MostowPrasadDescent
open D5.S3.Geometry.MostowPrasadCovering

namespace D5.S3.Geometry.IsometricOrbitMetric

variable {G X : Type*} [Group G] [MetricSpace X]

/-- Infimum distance between two representation orbits, independent of representatives. -/
noncomputable def orbitDistance (ρ : G →* (X ≃ᵢ X)) :
    OrbitQuotient ρ → OrbitQuotient ρ → ℝ :=
  Quotient.lift₂ (fun x y => infDist x (range (fun g => ρ g y))) (by
    intro x y x' y' hx hy
    rcases hx with ⟨a, rfl⟩
    rcases hy with ⟨b, rfl⟩
    have himage : (ρ a) '' range (fun g => ρ g y) =
        range (fun g => ρ g (ρ b y)) := by
      ext z
      constructor
      · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
        refine ⟨a * g * b⁻¹, ?_⟩
        simp [map_mul, IsometryEquiv.mul_apply]
      · rintro ⟨g, rfl⟩
        refine ⟨ρ (a⁻¹ * g * b) y, ⟨a⁻¹ * g * b, rfl⟩, ?_⟩
        simp [map_mul, IsometryEquiv.mul_apply]
    rw [← himage, infDist_image (ρ a).isometry])

/-- The orbit metric with the existing quotient topology for a properly discontinuous action. -/
@[instance_reducible]
noncomputable def orbitMetricSpace (ρ : G →* (X ≃ᵢ X))
    (hproper : ProperlyDiscontinuousRepresentation ρ) : MetricSpace (OrbitQuotient ρ) := by
  letI : MulAction G X := representationMulAction ρ
  letI : ContinuousConstSMul G X := ⟨fun g => (ρ g).continuous⟩
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : ProperlyDiscontinuousSMul G X := ⟨by
    intro K L hK hL
    exact hproper hK hL⟩
  letI : ProperSMul G X := properlyDiscontinuousSMul_iff_properSMul.mp inferInstance
  letI : T2Space (OrbitQuotient ρ) := (standardOrbitHomeomorph ρ).symm.t2Space
  have hne (y : X) : (range (fun g => ρ g y)).Nonempty :=
    ⟨ρ 1 y, ⟨1, rfl⟩⟩
  have hsymm (x y : X) : infDist x (range (fun g => ρ g y)) =
      infDist y (range (fun g => ρ g x)) := by
    suffices h : ∀ x y : X, infDist x (range (fun g => ρ g y)) ≤
        infDist y (range (fun g => ρ g x)) from le_antisymm (h x y) (h y x)
    intro u v
    apply (le_infDist (hne u)).2
    rintro _ ⟨g, rfl⟩
    calc
      infDist u (range (fun g => ρ g v)) ≤ dist u (ρ g⁻¹ v) :=
        infDist_le_dist_of_mem ⟨g⁻¹, rfl⟩
      _ = dist (ρ g u) v := by
        rw [← (ρ g).dist_eq u (ρ g⁻¹ v)]
        simp [← IsometryEquiv.mul_apply]
      _ = dist v (ρ g u) := dist_comm _ _
  refine MetricSpace.ofDistTopology (orbitDistance ρ) ?_ ?_ ?_ ?_ ?_
  · intro q
    induction q using Quotient.inductionOn' with
    | _ x =>
      exact infDist_zero_of_mem ⟨1, by simp⟩
  · intro q r
    induction q using Quotient.inductionOn' with
    | _ x =>
      induction r using Quotient.inductionOn' with
      | _ y => exact hsymm x y
  · intro q r s
    induction q using Quotient.inductionOn' with
    | _ x =>
      induction r using Quotient.inductionOn' with
      | _ y =>
        induction s using Quotient.inductionOn' with
        | _ z =>
          change infDist x (range (fun g => ρ g z)) ≤
            infDist x (range (fun g => ρ g y)) + infDist y (range (fun g => ρ g z))
          apply sub_le_iff_le_add.mp
          apply (le_infDist (hne y)).2
          rintro _ ⟨g, rfl⟩
          apply sub_le_iff_le_add.mpr
          apply sub_le_iff_le_add'.mp
          apply (le_infDist (hne z)).2
          rintro _ ⟨h, rfl⟩
          apply sub_le_iff_le_add'.mpr
          calc
            infDist x (range (fun g => ρ g z)) ≤ dist x (ρ (g * h) z) :=
              infDist_le_dist_of_mem ⟨g * h, rfl⟩
            _ ≤ dist x (ρ g y) + dist (ρ g y) (ρ (g * h) z) := dist_triangle _ _ _
            _ = dist x (ρ g y) + dist y (ρ h z) := by
              rw [map_mul, IsometryEquiv.mul_apply, (ρ g).dist_eq]
  · intro s
    rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
    constructor
    · intro hs q hq
      induction q using Quotient.inductionOn' with
      | _ x =>
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs x hq
        refine ⟨ε, hε, ?_⟩
        intro r hr
        induction r using Quotient.inductionOn' with
        | _ y =>
          obtain ⟨_, ⟨g, rfl⟩, hg⟩ := (infDist_lt_iff (hne y)).mp hr
          have hm := hball (by simpa [mem_ball, dist_comm] using hg)
          change Quotient.mk (orbitSetoid ρ) (ρ g y) ∈ s at hm
          rwa [← Quotient.sound (show (orbitSetoid ρ).r y (ρ g y) from ⟨g, rfl⟩)] at hm
    · intro hs
      apply Metric.isOpen_iff.mpr
      intro x hx
      obtain ⟨ε, hε, hball⟩ := hs (orbitQuotientMk ρ x) hx
      refine ⟨ε, hε, ?_⟩
      intro y hy
      apply hball (orbitQuotientMk ρ y)
      change infDist x (range (fun g => ρ g y)) < ε
      exact lt_of_le_of_lt (infDist_le_dist_of_mem (show y ∈ range (fun g => ρ g y) from
        ⟨1, by simp⟩))
        (by simpa [mem_ball, dist_comm] using hy)
  · intro q r
    induction q using Quotient.inductionOn' with
    | _ x =>
      induction r using Quotient.inductionOn' with
      | _ y =>
        intro hzero
        have hclosed : IsClosed (range (fun g => ρ g y)) := by
          convert (isClosed_singleton (x := Quotient.mk (orbitSetoid ρ) y)).preimage
            (continuous_quotient_mk' (s := orbitSetoid ρ)) using 1
          ext z
          change (∃ g, ρ g y = z) ↔
            Quotient.mk (orbitSetoid ρ) z = Quotient.mk (orbitSetoid ρ) y
          rw [Quotient.eq]
          constructor
          · rintro ⟨g, rfl⟩
            exact ⟨g⁻¹, by simp [← IsometryEquiv.mul_apply]⟩
          · rintro ⟨g, hg⟩
            refine ⟨g⁻¹, ?_⟩
            rw [← hg]
            simp [← IsometryEquiv.mul_apply]
        obtain ⟨g, hg⟩ := (hclosed.mem_iff_infDist_zero (hne y)).mpr hzero
        exact (Quotient.sound (show (orbitSetoid ρ).r y x from ⟨g, hg⟩)).symm

/-- Compact closed balls descend to the orbit metric quotient. -/
instance orbitProperSpace (ρ : G →* (X ≃ᵢ X))
    (hproper : ProperlyDiscontinuousRepresentation ρ) [ProperSpace X] :
    @ProperSpace (OrbitQuotient ρ) (orbitMetricSpace ρ hproper).toPseudoMetricSpace := by
  letI : MetricSpace (OrbitQuotient ρ) := orbitMetricSpace ρ hproper
  have hcont : Continuous (orbitQuotientMk ρ) := continuous_quotient_mk'
  refine ⟨fun q r => ?_⟩
  induction q using Quotient.inductionOn' with
  | _ x =>
    change IsCompact (closedBall (orbitQuotientMk ρ x) r)
    have hball : closedBall (orbitQuotientMk ρ x) r =
        orbitQuotientMk ρ '' closedBall x r := by
      ext q
      induction q using Quotient.inductionOn' with
      | _ y =>
        constructor
        · intro hy
          change orbitQuotientMk ρ y ∈ closedBall (orbitQuotientMk ρ x) r at hy
          have hclosed : IsClosed (range (fun g => ρ g y)) := by
            convert (isClosed_singleton (x := orbitQuotientMk ρ y)).preimage hcont using 1
            ext z
            change (∃ g, ρ g y = z) ↔
              Quotient.mk (orbitSetoid ρ) z = Quotient.mk (orbitSetoid ρ) y
            rw [Quotient.eq]
            constructor
            · rintro ⟨g, rfl⟩
              exact ⟨g⁻¹, by simp [← IsometryEquiv.mul_apply]⟩
            · rintro ⟨g, hg⟩
              refine ⟨g⁻¹, ?_⟩
              rw [← hg]
              simp [← IsometryEquiv.mul_apply]
          have hne : (range (fun g => ρ g y)).Nonempty := ⟨ρ 1 y, ⟨1, rfl⟩⟩
          obtain ⟨z, ⟨g, hg⟩, hmin⟩ := hclosed.exists_infDist_eq_dist hne x
          refine ⟨z, ?_, ?_⟩
          · rw [mem_closedBall, dist_comm, ← hmin]
            change dist (orbitQuotientMk ρ x) (orbitQuotientMk ρ y) ≤ r
            simpa [mem_closedBall, dist_comm] using hy
          · exact (Quotient.sound (show (orbitSetoid ρ).r y z from ⟨g, hg⟩)).symm
        · rintro ⟨z, hz, hzy⟩
          rw [← hzy, mem_closedBall, dist_comm]
          change infDist x (range (fun g => ρ g z)) ≤ r
          exact (infDist_le_dist_of_mem (show z ∈ range (fun g => ρ g z) from
            ⟨1, by simp⟩)).trans (by simpa [mem_closedBall, dist_comm] using hz)
    rw [hball]
    exact (isCompact_closedBall x r).image hcont

#print axioms orbitDistance
#print axioms orbitMetricSpace
#print axioms orbitProperSpace

end D5.S3.Geometry.IsometricOrbitMetric
