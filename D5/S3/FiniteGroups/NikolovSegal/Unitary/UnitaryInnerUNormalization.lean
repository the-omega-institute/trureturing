/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryInnerUNormalization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryInnerUNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryPositiveSylow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NikolovSegal.UnitarySylow
open Matrix SLnNormalizer PartIIUnitaryUpperTorus PartIIUnitriangularLayers
universe u
variable {F : Type u} [Field F] [Finite F] {n : ℕ}

/-- The subgroup is the literal determinant-one anti-diagonal Hermitian carrier. -/
theorem mem_specialUnitary_iff_hermitian (ι : RingAut F)
    (hinv : Function.Involutive ι) (g : SpecialLinearGroup (Fin n) F) :
    g ∈ specialUnitary n ι ↔
      UnitaryField.adjoint ι g.val *
        UnitaryField.antiDiagonal n * g.val =
          UnitaryField.antiDiagonal n :=
  PartIIUnitaryTorusSupply.actual_steinberg_iff_hermitian ι hinv g

/-- Every bare actual SU automorphism admits one genuine SU inner correction
before all targets. Native finite Sylow conjugacy is applied to the proved
literal Sylow, and native normalizer functoriality preserves its actual Borel. -/
theorem inner_positiveU_correction (p : ℕ) [Fact p.Prime] [CharP F p]
    (n : ℕ) (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (alpha : MulAut (specialUnitary n ι)) :
    ∃ h : specialUnitary n ι, let beta := MulAut.conj h * alpha
      (positiveU n ι).map beta.toMonoidHom = positiveU n ι ∧
      (∀ g : specialUnitary n ι, beta g ∈ positiveU n ι ↔ g ∈ positiveU n ι) ∧
      (∀ g : specialUnitary n ι,
        LayerDepth 1 ((beta g).val.val-1) ↔ LayerDepth 1 (g.val.val-1)) ∧
      (∀ g : specialUnitary n ι, Upper (beta g).val ↔ Upper g.val) := by
  let P := positiveUSylow p n ι hinv hne
  let Q := P.mapSurjective (f := alpha.toMonoidHom) alpha.surjective
  obtain ⟨h,hh⟩ := MulAction.exists_smul_eq (specialUnitary n ι) Q P
  let beta := MulAut.conj h * alpha
  have he := congrArg (fun R : Sylow p (specialUnitary n ι) => R.toSubgroup) hh
  change ((positiveU n ι).map alpha.toMonoidHom).map (MulAut.conj h).toMonoidHom =
    positiveU n ι at he
  have hU : (positiveU n ι).map beta.toMonoidHom=positiveU n ι := by
    change (positiveU n ι).map ((MulAut.conj h).toMonoidHom.comp alpha.toMonoidHom)=_
    rwa [←Subgroup.map_map]
  have hN : (Subgroup.normalizer (positiveU n ι : Set (specialUnitary n ι))).map beta.toMonoidHom =
    Subgroup.normalizer (positiveU n ι : Set (specialUnitary n ι)) := by
    rw [Subgroup.map_equiv_normalizer_eq,hU]
  have hUi : ∀ g : specialUnitary n ι, beta g∈positiveU n ι ↔ g∈positiveU n ι := by
    intro g
    have hm := Subgroup.mem_map_iff_mem (f := beta.toMonoidHom)
      (K := positiveU n ι) (x := g) beta.injective
    rwa [hU] at hm
  refine ⟨h,hU,hUi,?_,?_⟩
  · intro g
    simpa only [←mem_positiveU_iff] using hUi g
  · intro g
    have hm := Subgroup.mem_map_iff_mem (f := beta.toMonoidHom)
      (K := Subgroup.normalizer (positiveU n ι : Set (specialUnitary n ι))) (x := g) beta.injective
    rw [hN,mem_normalizer_iff_upper ι hinv hne,mem_normalizer_iff_upper ι hinv hne] at hm
    exact hm

end NikolovSegal.UnitarySylow
