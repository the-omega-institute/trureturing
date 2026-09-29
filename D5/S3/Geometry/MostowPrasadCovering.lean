/- GID: D5/S3/Geometry/MostowPrasadCovering
   generality: G
   mirror-B: D5/B/S3/Geometry/MostowPrasadCovering
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Geometry.Manifold.Instances.Quotient]
   utility: none
   digest: Connect isometric representations to standard orbit quotients and their covering maps. -/

import D5.S3.Geometry.MostowPrasadDescent
import Mathlib.Geometry.Manifold.Instances.Quotient
import Mathlib.Topology.Homeomorph.Quotient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

namespace D5.S3.Geometry.MostowPrasadCovering

open D5.S3.Geometry.MostowPrasadDescent

variable {G X : Type*} [Group G] [MetricSpace X]

/-- An isometric representation, viewed as a group action on its metric space. -/
@[instance_reducible]
def representationMulAction (ρ : G →* (X ≃ᵢ X)) : MulAction G X where
  smul g x := ρ g x
  one_smul x := by
    change ρ 1 x = x
    simp
  mul_smul g h x := by
    change ρ (g * h) x = ρ g (ρ h x)
    rw [map_mul, IsometryEquiv.mul_apply]

/-- Mathlib's orbit quotient for the action associated with a representation. -/
abbrev StandardOrbitQuotient (ρ : G →* (X ≃ᵢ X)) : Type _ :=
  letI : MulAction G X := representationMulAction ρ
  MulAction.orbitRel.Quotient G X

/-- Pointwise freeness of the isometric representation. -/
def FreeRepresentation (ρ : G →* (X ≃ᵢ X)) : Prop :=
  ∀ (g : G) (x : X), ρ g x = x → g = 1

/-- Proper discontinuity expressed directly in terms of the isometric representation. -/
def ProperlyDiscontinuousRepresentation (ρ : G →* (X ≃ᵢ X)) : Prop :=
  ∀ {K L : Set X}, IsCompact K → IsCompact L →
    Set.Finite {g : G | ((ρ g : X → X) '' K ∩ L).Nonempty}

private theorem orbitRel_iff (ρ : G →* (X ≃ᵢ X)) (x y : X) :
    (orbitSetoid ρ).r x y ↔
      letI : MulAction G X := representationMulAction ρ
      (MulAction.orbitRel G X).r x y := by
  letI : MulAction G X := representationMulAction ρ
  change (∃ g : G, ρ g x = y) ↔ (∃ g : G, ρ g y = x)
  constructor
  · rintro ⟨g, h⟩
    refine ⟨g⁻¹, ?_⟩
    calc
      ρ g⁻¹ y = ρ g⁻¹ (ρ g x) := by rw [h]
      _ = ρ (g⁻¹ * g) x := by rw [map_mul, IsometryEquiv.mul_apply]
      _ = x := by simp
  · rintro ⟨g, h⟩
    refine ⟨g⁻¹, ?_⟩
    calc
      ρ g⁻¹ x = ρ g⁻¹ (ρ g y) := by rw [h]
      _ = ρ (g⁻¹ * g) y := by rw [map_mul, IsometryEquiv.mul_apply]
      _ = y := by simp

/-- The custom orbit quotient is homeomorphic to Mathlib's standard orbit quotient. -/
noncomputable def standardOrbitHomeomorph (ρ : G →* (X ≃ᵢ X)) :
    OrbitQuotient ρ ≃ₜ StandardOrbitQuotient ρ := by
  letI : MulAction G X := representationMulAction ρ
  exact Homeomorph.Quotient.congrRight (orbitRel_iff ρ)

/-- A free, properly discontinuous isometric representation gives a covering projection. -/
theorem orbitQuotientMk_isCoveringMap (ρ : G →* (X ≃ᵢ X))
    [LocallyCompactSpace X]
    (hfree : FreeRepresentation ρ)
    (hproper : ProperlyDiscontinuousRepresentation ρ) :
    IsCoveringMap (orbitQuotientMk ρ) := by
  letI : MulAction G X := representationMulAction ρ
  letI : ContinuousConstSMul G X := ⟨fun g => (ρ g).continuous⟩
  letI : ProperlyDiscontinuousSMul G X := ⟨by
    intro K L hK hL
    exact hproper hK hL⟩
  letI : IsCancelSMul G X :=
    isCancelSMul_iff_eq_one_of_smul_eq.mpr hfree
  have hstandard : IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel G X)) G :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  have hcustom := hstandard.homeomorph_comp (standardOrbitHomeomorph ρ).symm
  convert hcustom.isCoveringMap using 1
  funext x
  rfl

#print axioms standardOrbitHomeomorph
#print axioms orbitQuotientMk_isCoveringMap

end D5.S3.Geometry.MostowPrasadCovering
