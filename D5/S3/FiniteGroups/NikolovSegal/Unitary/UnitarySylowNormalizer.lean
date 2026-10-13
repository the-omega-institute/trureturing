/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowNormalizer
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowNormalizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitarySylowFlag

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NikolovSegal.UnitarySylow
open Matrix SLnNormalizer PartIIUnitaryUpperTorus
universe u
variable {F : Type u} [Field F] [Finite F] {n : ℕ}

/-- Every prefix is preserved by a normalizer element, from the intrinsic
unitary-root characterization rather than an assumed fixed flag. -/
theorem normalizer_preserves_prefix (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι ≠ RingEquiv.refl F) (g : specialUnitary n ι)
    (hg : g  ∈  Subgroup.normalizer (positiveU n ι : Set (specialUnitary n ι)))
    (k : ℕ) (v : Fin n → F) (hv : Prefix k v) : Prefix k (g.val.val *ᵥ v) := by
  induction k generalizing v with
  | zero =>
    have he : v=0 := funext fun i => hv i (Nat.zero_le _)
    subst v
    intro i _
    simp
  | succ k ih =>
    apply (prefix_succ_iff ι hinv hne k _).mpr
    intro h hh
    have hc : g⁻¹*h*g ∈ positiveU n ι :=
      (Subgroup.mem_normalizer_iff''.mp hg h).mp hh
    have hp := ih _ ((prefix_succ_iff ι hinv hne k v).mp hv _ hc)
    have he : h.val.val *ᵥ (g.val.val *ᵥ v)-g.val.val *ᵥ v =
      g.val.val *ᵥ ((g⁻¹*h*g).val.val *ᵥ v-v) := by
      simp only [Matrix.mulVec_sub,Matrix.mulVec_mulVec,
        ← SpecialLinearGroup.coe_mul,← Subgroup.coe_mul,← Subgroup.coe_inv]
      simp [←mul_assoc]
    rw [he]
    exact hp

/-- The genuine SU normalizer has literal zero entries below the diagonal. -/
theorem upper_of_normalizer (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι ≠ RingEquiv.refl F) (g : specialUnitary n ι)
    (hg : g  ∈  Subgroup.normalizer (positiveU n ι : Set (specialUnitary n ι))) :
    Upper g.val := by
  intro r c hrc
  have hv : Prefix (c.val+1) (Pi.single c (1:F)) := by
    intro i hi
    have hne' : c ≠ i := fun he => by subst i;omega
    simp [Pi.single_apply,hne']
  have hp := normalizer_preserves_prefix ι hinv hne g hg (c.val+1) _ hv r (by omega)
  simpa [Matrix.mulVec_single_one] using hp

/-- Exact normalizer recognition for actual positive unitary U. -/
theorem mem_normalizer_iff_upper (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι ≠ RingEquiv.refl F) (g : specialUnitary n ι) :
    g  ∈  Subgroup.normalizer (positiveU n ι : Set (specialUnitary n ι)) ↔ Upper g.val := by
  refine ⟨upper_of_normalizer ι hinv hne g,fun hg => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact SLnNormalizer.conjugate_mem_Uplus_of_upper g.val hg h.val hh
  · intro hh
    have hm := SLnNormalizer.conjugate_mem_Uplus_of_upper g.val⁻¹ (upper_inv hg)
      (g*h*g⁻¹).val hh
    change h.val ∈ Uplus n F
    simpa [mul_assoc] using hm

end NikolovSegal.UnitarySylow
