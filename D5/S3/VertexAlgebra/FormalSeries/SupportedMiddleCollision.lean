/- GID: D5/S3/VertexAlgebra/FormalSeries/SupportedMiddleCollision
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/SupportedMiddleCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Legal outer collision with the middle exponent held fixed. -/
import D5.S3.VertexAlgebra.FormalSeries.SupportedThreeFieldCollision

/-! Reuse the proved spectator collision by the label permutation 0 <-> 1.
All substitution maps have zero constant coefficients. This module supplies
only native-series identities; the sector module proves the actual Jacobi
identification before consuming them. Carnahan attribution stays in the
original supported-binomial supplier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.SupportedMiddleCollision
open SupportedChannelSeries SupportedThreeFieldCollision
open UngradedLocalWordSeries UniformGradedLocalCorrelator
noncomputable section

private def swap01 : Fin 3 ≃ Fin 3 := Equiv.swap 0 1

private theorem swap_index (s b z : ℕ) :
    (index3 b s z).embDomain swap01.toEmbedding = index3 s b z := by
  simp [index3, Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single, swap01, Equiv.swap_apply_def, add_comm, add_left_comm, add_assoc]

private theorem swap_signed {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (s b z : ℤ) :
    signedExtend (MvPowerSeries.rename swap01 P) ![s, b, z] =
      signedExtend P ![b, s, z] := by
  classical
  have nn : (∀ i : Fin 3, 0 ≤ (![s, b, z] : Fin 3 → ℤ) i) ↔
      (∀ i : Fin 3, 0 ≤ (![b, s, z] : Fin 3 → ℤ) i) := by
    constructor <;> intro h i <;> fin_cases i
    · exact h 1
    · exact h 0
    · exact h 2
    · exact h 1
    · exact h 0
    · exact h 2
  by_cases h : ∀ i : Fin 3, 0 ≤ (![s, b, z] : Fin 3 → ℤ) i
  · rw [signedExtend, if_pos h, signedExtend, if_pos (nn.mp h)]
    have idx (x y t : ℤ) : signedIndex (![x, y, t] : Fin 3 → ℤ) =
        index3 x.toNat y.toNat t.toNat := by
      ext i
      fin_cases i <;> simp [signedIndex, index3]
    rw [idx, idx, ← swap_index s.toNat b.toNat z.toNat]
    exact MvPowerSeries.coeff_embDomain_rename swap01.toEmbedding P _
  · simp only [signedExtend, if_neg h, if_neg (fun h' => h (nn.mpr h'))]

/-- Genuine bivariate native series at a fixed signed middle exponent.
It is identically zero for b<0; there is no support assumption on P. -/
def middleNativeSlice {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (b : ℤ) : MvPowerSeries (Fin 2) R :=
  slice (MvPowerSeries.rename swap01 P) b

/-- Full outer substitution z0=s+z, with the middle coordinate fixed. -/
def outerArguments (R : Type*) [CommRing R] : Fin 3 → MvPowerSeries (Fin 3) R :=
  ![MvPowerSeries.X 0 + MvPowerSeries.X 2, MvPowerSeries.X 1, MvPowerSeries.X 2]

private theorem outer_hasSubst (R : Type*) [CommRing R] :
    MvPowerSeries.HasSubst (outerArguments R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [outerArguments]

/-- Signed slice equality, including every negative-coordinate zero case. -/
theorem middleNativeSlice_extend {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (b s z : ℤ) :
    extend (middleNativeSlice P b) s z = signedExtend P ![s, b, z] := by
  rw [middleNativeSlice, slice_extend, swap_signed]

private theorem outer_as_swapped_inner {R : Type*} [CommRing R]
    (P : MvPowerSeries (Fin 3) R) :
    MvPowerSeries.subst (outerArguments R) P =
      MvPowerSeries.rename swap01 (innerCollision (MvPowerSeries.rename swap01 P)) := by
  let r : Fin 3 → MvPowerSeries (Fin 3) R := MvPowerSeries.X ∘ swap01
  have hr : MvPowerSeries.HasSubst r := MvPowerSeries.HasSubst.X_comp _
  have hi : MvPowerSeries.HasSubst (innerArguments R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    fin_cases i <;> simp [innerArguments]
  have hc : MvPowerSeries.HasSubst
      (fun i => MvPowerSeries.subst (innerArguments R) (r i)) := by
    simpa only [MvPowerSeries.substAlgHom_apply] using hr.comp hi
  rw [MvPowerSeries.rename_eq_subst, innerCollision, MvPowerSeries.rename_eq_subst]
  change _ = MvPowerSeries.subst r (MvPowerSeries.subst (innerArguments R)
    (MvPowerSeries.subst r P))
  rw [MvPowerSeries.subst_comp_subst_apply hr hi,
    MvPowerSeries.subst_comp_subst_apply hc hr]
  congr 1
  funext i
  simp only [r, Function.comp_apply, MvPowerSeries.subst_X hi]
  fin_cases i
  · change MvPowerSeries.X 0 + MvPowerSeries.X 2 =
      MvPowerSeries.subst r (MvPowerSeries.X 1 + MvPowerSeries.X 2)
    rw [MvPowerSeries.subst_add hr, MvPowerSeries.subst_X hr, MvPowerSeries.subst_X hr]
    simp [r, swap01, Equiv.swap_apply_def]
  · change MvPowerSeries.X 1 = MvPowerSeries.subst r (MvPowerSeries.X 0)
    rw [MvPowerSeries.subst_X hr]
    simp [r, swap01]
  · change MvPowerSeries.X 2 = MvPowerSeries.subst r (MvPowerSeries.X 2)
    rw [MvPowerSeries.subst_X hr]
    simp [r, swap01, Equiv.swap_apply_def]


/-- Actual legal outer collision equals the signed bivariate collision on
its fixed middle slice. No statement about canonical iterates is assumed. -/
theorem outerCollision_signed {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (b s z : ℤ) :
    signedExtend (MvPowerSeries.subst (outerArguments R) P) ![s, b, z] =
      extend (collision (middleNativeSlice P b)) s z := by
  rw [outer_as_swapped_inner, swap_signed]
  exact innerCollision_signed (MvPowerSeries.rename swap01 P) b s z

/-- The exact simultaneous coordinates after the two legal substitutions. -/
def middleArguments (R : Type*) [CommRing R] : Fin 3 → MvPowerSeries (Fin 3) R :=
  ![MvPowerSeries.X 0 + MvPowerSeries.X 2,
    MvPowerSeries.X 1 + MvPowerSeries.X 2, MvPowerSeries.X 2]

/-- Two legal substitutions retain the very same input P. -/
theorem outer_inner_substitution {R : Type*} [CommRing R]
    (P : MvPowerSeries (Fin 3) R) :
    MvPowerSeries.subst (outerArguments R) (innerCollision P) =
      MvPowerSeries.subst (middleArguments R) P := by
  have hi : MvPowerSeries.HasSubst (innerArguments R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    fin_cases i <;> simp [innerArguments]
  rw [innerCollision, MvPowerSeries.subst_comp_subst_apply hi (outer_hasSubst R)]
  congr 1
  funext i
  fin_cases i
  · change MvPowerSeries.subst (outerArguments R) (MvPowerSeries.X 0) = _
    rw [MvPowerSeries.subst_X (outer_hasSubst R)]
    rfl
  · change MvPowerSeries.subst (outerArguments R) (MvPowerSeries.X 1 + MvPowerSeries.X 2) = _
    rw [MvPowerSeries.subst_add (outer_hasSubst R),
      MvPowerSeries.subst_X (outer_hasSubst R), MvPowerSeries.subst_X (outer_hasSubst R)]
    rfl
  · change MvPowerSeries.subst (outerArguments R) (MvPowerSeries.X 2) = _
    rw [MvPowerSeries.subst_X (outer_hasSubst R)]
    rfl

end
end D5.S3.VertexAlgebra.SupportedMiddleCollision
