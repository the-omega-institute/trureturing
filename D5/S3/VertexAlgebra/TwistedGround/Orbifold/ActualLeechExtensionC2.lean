/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sector quotient classes surject onto the literal C2 quotient of the assembled extension. -/

import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2Cofinite
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldField

set_option autoImplicit false

noncomputable section

open scoped VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionC2

open ActualLeechHyperbolic (leechData leech_spec)
open HalfFock.LatticeHalfFockParityField (fixedParitySlice paritySpace)
open Lattice.ActualFixedC2 (fixedC2 leech_fixed_c2_cofinite)
open LatticeGeneratingFieldLocality (LatticeData)
open LatticeInvolution (FixedCarrier fixedMode fixedSpace)
open OriginalOrbifoldField (Carrier Y)

local instance (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

local instance (D : LatticeData) (hu : IsUnit D.G.det) :
    AddCommGroup (paritySpace D hu (-1)) :=
  (paritySpace D hu (-1)).addCommGroup

variable (D : LatticeData) (hu : IsUnit D.G.det)
variable (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

/-- The actual fixed-source `(-2)`-action on the negative twisted sector. -/
def relativeOddMinusTwo (u : FixedCarrier D) (t : paritySpace D hu (-1)) :
    paritySpace D hu (-1) :=
  ((fixedParitySlice D hu (-1) u)[[-2]]) t

/-- The relative C₂ subspace of the actual negative twisted sector. -/
def relativeOddC2 : Submodule ℂ (paritySpace D hu (-1)) :=
  Submodule.span ℂ {z | ∃ (u : FixedCarrier D) (t : paritySpace D hu (-1)),
    z = relativeOddMinusTwo D hu u t}

/-- The `(-2)`-product of two states of the assembled extension. -/
def extensionMinusTwo (a b : Carrier D hu) : Carrier D hu :=
  ((Y D hu hD a)[[-2]]) b

/-- The C₂ subspace of the extension, using all states as both inputs. -/
def extensionC2 : Submodule ℂ (Carrier D hu) :=
  Submodule.span ℂ {z | ∃ a b : Carrier D hu, z = extensionMinusTwo D hu hD a b}

/-- The two coordinates of the assembled `(-2)`-mode with fixed source. -/
theorem fixed_source_minus_two (u v : FixedCarrier D) (t : paritySpace D hu (-1)) :
    extensionMinusTwo D hu hD (u, 0) (v, t) =
      (fixedMode D u (-2) v, relativeOddMinusTwo D hu u t) :=
  OriginalOrbifoldField.Y_fixed_ncoeff_apply D hu hD (-2) u (v, t)

theorem fixed_fixed_minus_two (u v : FixedCarrier D) :
    extensionMinusTwo D hu hD (u, 0) (v, 0) = (fixedMode D u (-2) v, 0) := by
  rw [extensionMinusTwo, OriginalOrbifoldField.Y_ncoeff_apply]
  simp only [map_zero, LinearMap.zero_apply, add_zero]

theorem fixed_odd_minus_two (u : FixedCarrier D) (t : paritySpace D hu (-1)) :
    extensionMinusTwo D hu hD (u, 0) (0, t) = (0, relativeOddMinusTwo D hu u t) := by
  rw [fixed_source_minus_two, map_zero]

theorem fixedC2_le_comap_inl : fixedC2 D ≤ (extensionC2 D hu hD).comap
    (LinearMap.inl ℂ (FixedCarrier D) (paritySpace D hu (-1))) := by
  rw [fixedC2, Submodule.span_le]
  rintro _ ⟨u, v, rfl⟩
  change ((fixedMode D u (-2) v, 0) : Carrier D hu) ∈ extensionC2 D hu hD
  rw [← fixed_fixed_minus_two D hu hD]
  exact Submodule.subset_span ⟨(u, 0), (v, 0), rfl⟩

theorem relativeOddC2_le_comap_inr : relativeOddC2 D hu ≤ (extensionC2 D hu hD).comap
    (LinearMap.inr ℂ (FixedCarrier D) (paritySpace D hu (-1))) := by
  rw [relativeOddC2, Submodule.span_le]
  rintro _ ⟨u, t, rfl⟩
  change ((0, relativeOddMinusTwo D hu u t) : Carrier D hu) ∈ extensionC2 D hu hD
  rw [← fixed_odd_minus_two D hu hD]
  exact Submodule.subset_span ⟨(u, 0), (0, t), rfl⟩

/-- Add representatives on the two axes and take their class in the extension. -/
def quotientComparison :
    ((FixedCarrier D ⧸ fixedC2 D) × (paritySpace D hu (-1) ⧸ relativeOddC2 D hu)) →ₗ[ℂ]
      (Carrier D hu ⧸ extensionC2 D hu hD) :=
  ((fixedC2 D).mapQ (extensionC2 D hu hD)
    (LinearMap.inl ℂ (FixedCarrier D) (paritySpace D hu (-1)))
    (fixedC2_le_comap_inl D hu hD)).coprod
    ((relativeOddC2 D hu).mapQ (extensionC2 D hu hD)
      (LinearMap.inr ℂ (FixedCarrier D) (paritySpace D hu (-1)))
      (relativeOddC2_le_comap_inr D hu hD))

@[simp]
theorem quotientComparison_mk (v : FixedCarrier D) (t : paritySpace D hu (-1)) :
    quotientComparison D hu hD ((fixedC2 D).mkQ v, (relativeOddC2 D hu).mkQ t) =
      (extensionC2 D hu hD).mkQ (v, t) := by
  change (extensionC2 D hu hD).mkQ ((v, 0) : Carrier D hu) +
    (extensionC2 D hu hD).mkQ ((0, t) : Carrier D hu) = _
  rw [← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

theorem quotientComparison_surjective : Function.Surjective (quotientComparison D hu hD) := by
  intro q
  obtain ⟨⟨v, t⟩, rfl⟩ := (extensionC2 D hu hD).mkQ_surjective q
  exact ⟨((fixedC2 D).mkQ v, (relativeOddC2 D hu).mkQ t),
    quotientComparison_mk D hu hD v t⟩

local notation "uΛ" => And.left (And.right leech_spec)
local notation "pΛ" => And.left (And.right (And.right leech_spec))

abbrev LeechFixedQuotient := FixedCarrier leechData ⧸ fixedC2 leechData

abbrev LeechRelativeOddQuotient := paritySpace leechData uΛ (-1) ⧸ relativeOddC2 leechData uΛ

abbrev LeechExtensionQuotient := Carrier leechData uΛ ⧸ extensionC2 leechData uΛ pΛ

/-- The comparison on the chosen positive definite unimodular Leech realization. -/
def leechQuotientComparison :
    LeechFixedQuotient × LeechRelativeOddQuotient →ₗ[ℂ] LeechExtensionQuotient :=
  quotientComparison leechData uΛ pΛ

theorem leechQuotientComparison_surjective : Function.Surjective leechQuotientComparison :=
  quotientComparison_surjective leechData uΛ pΛ

/-- Finite dimensionality of the actual negative twisted relative quotient suffices. -/
theorem leech_extension_c2_cofinite_of_relative_odd_finite
    (hOdd : FiniteDimensional ℂ LeechRelativeOddQuotient) :
    FiniteDimensional ℂ LeechExtensionQuotient := by
  let : FiniteDimensional ℂ LeechFixedQuotient := leech_fixed_c2_cofinite
  let : FiniteDimensional ℂ LeechRelativeOddQuotient := hOdd
  exact FiniteDimensional.of_surjective leechQuotientComparison leechQuotientComparison_surjective

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionC2
