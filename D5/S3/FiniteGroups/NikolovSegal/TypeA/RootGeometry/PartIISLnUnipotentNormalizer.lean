/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.SLnUnitriangular

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The normalizer of the actual full upper unitriangular subgroup of SLn,
over every field, in every rank. The canonical coordinate prefixes are derived
intrinsically from the subgroup action, using coefficient-one transvections. -/
namespace NikolovSegal.SLnNormalizer
open Matrix
universe u
variable {F : Type u} [Field F] {n : ℕ}

/-- Vectors supported on the first k coordinates; no bound on k is imposed. -/
def Prefix (k : ℕ) (v : Fin n → F) : Prop :=
  ∀ i : Fin n, k ≤ i.val → v i = 0

/-- The actual unitriangular action recovers the next coordinate prefix.
The reverse direction uses E_(k,j)(1), so works also in characteristics 2/3. -/
theorem prefix_succ_iff (k : ℕ) (v : Fin n → F) :
    Prefix (k+1) v ↔
      ∀ h : SpecialLinearGroup (Fin n) F, h ∈ Uplus n F →
        Prefix k (h.val *ᵥ v - v) := by
  constructor
  · intro hv h hh i hki
    change (h.val *ᵥ v) i - v i = 0
    rw [sub_eq_zero]
    change ∑ j : Fin n, h.val i j * v j = v i
    have hs : ∑ j : Fin n, h.val i j * v j = h.val i i * v i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        by_cases hj : j.val < i.val
        · simp [(mem_Uplus_iff h).mp hh |>.1 i j hj]
        · have hij : i.val < j.val := by
            have hne : j.val ≠ i.val := fun he => hji (Fin.ext he)
            omega
          rw [hv j (by omega), mul_zero]
      · simp
    rw [hs, (mem_Uplus_iff h).mp hh |>.2 i, one_mul]
  · intro hv j hj
    let i : Fin n := ⟨k, by omega⟩
    have hij : i.val < j.val := by dsimp [i]; omega
    have ht := hv (SpecialLinearGroup.transvection (ne_of_lt (show i < j from hij)) (1:F))
      (transvection_mem_Uplus hij 1) i (by dsimp [i]; omega)
    simpa [SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.single_mulVec, Function.update_apply] using ht

/-- Normalization preserves every coordinate prefix, derived by induction
from the actual conjugation law and the intrinsic action characterization. -/
theorem normalizer_preserves_prefix (g : SpecialLinearGroup (Fin n) F)
    (hg : g ∈ Subgroup.normalizer (Uplus n F : Set (SpecialLinearGroup (Fin n) F)))
    (k : ℕ) (v : Fin n → F) (hv : Prefix k v) : Prefix k (g.val *ᵥ v) := by
  induction k generalizing v with
  | zero =>
    have he : v = 0 := funext fun i => hv i (Nat.zero_le _)
    subst v
    intro i _
    simp
  | succ k ih =>
    apply (prefix_succ_iff k _).mpr
    intro h hh
    have hconj : g⁻¹*h*g ∈ Uplus n F :=
      (Subgroup.mem_normalizer_iff''.mp hg h).mp hh
    have hv' := (prefix_succ_iff k v).mp hv (g⁻¹*h*g) hconj
    have hp := ih _ hv'
    have he : h.val *ᵥ (g.val *ᵥ v) - g.val *ᵥ v =
        g.val *ᵥ ((g⁻¹*h*g).val *ᵥ v - v) := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul]
      simp [← mul_assoc]
    rw [he]
    exact hp

/-- A normalizer element has the actual zero entries below its diagonal. -/
theorem below_diagonal_zero_of_normalizer (g : SpecialLinearGroup (Fin n) F)
    (hg : g ∈ Subgroup.normalizer (Uplus n F : Set (SpecialLinearGroup (Fin n) F))) :
    Upper g := by
  intro r c hrc
  have hv : Prefix (c.val+1) (Pi.single c (1:F)) := by
    intro i hi
    have hne : c ≠ i := fun he => by subst i; omega
    simp [Pi.single_apply, hne]
  have hp := normalizer_preserves_prefix g hg (c.val+1) _ hv r (by omega)
  simpa [Matrix.mulVec_single_one] using hp

/-- Upper triangular conjugation preserves the literal unitriangular carrier. -/
theorem conjugate_mem_Uplus_of_upper (g : SpecialLinearGroup (Fin n) F)
    (hg : Upper g) (h : SpecialLinearGroup (Fin n) F) (hh : h ∈ Uplus n F) :
    g*h*g⁻¹ ∈ Uplus n F := by
  obtain ⟨hht,hhd⟩ := (mem_Uplus_iff h).mp hh
  have hgi := upper_inv hg
  have hgh := upper_mul hg hht
  apply (mem_Uplus_iff _).mpr
  refine ⟨upper_mul hgh hgi, ?_⟩
  intro i
  rw [upper_mul_diag hgh hgi i, upper_mul_diag hg hht i, hhd i,
    mul_one, ← upper_mul_diag hg hgi i, mul_inv_cancel]
  simp

/-- Literal normalizer/Borel recognition, with no rank or field-size bound. -/
theorem mem_normalizer_iff_upper (g : SpecialLinearGroup (Fin n) F) :
    g ∈ Subgroup.normalizer (Uplus n F : Set (SpecialLinearGroup (Fin n) F)) ↔
      ∀ r c : Fin n, c.val < r.val → g.val r c = 0 := by
  refine ⟨below_diagonal_zero_of_normalizer g, fun hg => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conjugate_mem_Uplus_of_upper g hg h
  · intro hh
    have hm := conjugate_mem_Uplus_of_upper g⁻¹ (upper_inv hg) _ hh
    simpa [mul_assoc] using hm

/-- Equality with the actual determinant-one upper triangular subgroup. -/
theorem normalizer_eq_Borel :
    Subgroup.normalizer (Uplus n F : Set (SpecialLinearGroup (Fin n) F)) = Borel n F := by
  ext g
  exact mem_normalizer_iff_upper g

end NikolovSegal.SLnNormalizer
