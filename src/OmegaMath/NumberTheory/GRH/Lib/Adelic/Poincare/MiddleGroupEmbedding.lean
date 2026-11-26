import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.Bruhat.BigCell
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Poincaré series along a Bessel subgroup, unfolding; unipotent strong approximation
(known result; see Lib.Adelic.Poincare.BesselSubgroup).

Set-up used by: Poincaré series along a Bessel subgroup, unfolding; unipotent strong approximation.

This file: Block embedding of U(k) onto the reductive part H of the Bessel subgroup. -/

attribute [local simp] Matrix.mul_apply splitGram

attribute [local simp←] Matrix.ext_iff

/-- The embedding of the unitary group of the identity form on A^κ into the unitary group of the
whole space with middle form `Shape.middleGram` N,
acting on X₀ and fixing the other basis vectors. -/
@[local simp, simps! -isSimp apply_coe_val] noncomputable def toBesselH {A} [CommRing A] [StarRing
  A] (𝔰 : Shape) (N : A) := ((Units.map
  ⟨⟨(Matrix.fromBlocks 1 0 0 <| ·.fromBlocks 0 0 1 |>.fromBlocks 0 0 1), by simp⟩, by simp⟩).comp
  (U 1).subtype).codRestrict (𝔰.middleGram N).G (by simp [↓mem_U, middleGram])

variable {A : Type} [CommRing A] [StarRing A] {𝔰} {N : A}

@[simp] lemma toBesselH_mem u : toBesselH 𝔰 N u ∈ besselH := by aesop_cat

lemma exists_toBesselH_eq {h} (hh : h ∈ besselH) (hN : IsUnit N := by simp) : ∃ u, h =
  toBesselH 𝔰 N u := by
  cases by simpa [floorGroup_apply hh, mem_U, middleGram, hN.mul_right_eq_zero] using h.2
  use U.of (by simp)
    (h.1.1.submatrix 𝔰.indexX₀ 𝔰.indexX₀) ?_ <;> ext : 2 <;> simp [floorGroup_apply hh] <;> aesop

lemma exists_besselU_mul_toBesselH [TraceOne A] [IsHermUnit (𝔰.middleGram N).splitGram] {s} (h :
  s ∈ besselS) (hN : IsUnit N := by simp) :
  ∃ u ∈ besselU, ∃ g, s = u * toBesselH 𝔰 N g := by grind [mem_besselS, exists_toBesselH_eq]
