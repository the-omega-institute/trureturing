/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitarySylowCarrier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnUnipotentSylow
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnUnipotentNormalizer
import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryTorusSupply
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryRankTwoGeometry
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryTraceRoot
import Mathlib.GroupTheory.Nilpotent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NikolovSegal.UnitarySylow
open Matrix SLnNormalizer PartIIUnitaryUpperTorus PartIIUnitriangularLayers
universe u
variable {F : Type u} [Field F] {n : ℕ}

/-- Literal determinant-one anti-diagonal unitary group: fixed points of the
accepted field/inverse-transpose Steinberg automorphism on actual SL. -/
def specialUnitary (n : ℕ) (ι : RingAut F) :
    Subgroup (SpecialLinearGroup (Fin n) F) where
  carrier := {g | steinberg ι g = g}
  one_mem' := map_one _
  mul_mem' := by
    intro a b ha hb
    change steinberg ι (a*b)=a*b
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    change steinberg ι a⁻¹=a⁻¹
    rw [map_inv, ha]

/-- Exactly the literal positive unitriangular matrices in actual SU. -/
def positiveU (n : ℕ) (ι : RingAut F) : Subgroup (specialUnitary n ι) :=
  (Uplus n F).comap (specialUnitary n ι).subtype

theorem unitriangular_iff_depth (g : SpecialLinearGroup (Fin n) F) :
    g ∈ Uplus n F ↔ LayerDepth 1 (g.val-1) := by
  constructor
  · rintro ⟨hg,hd⟩ i j hij
    by_cases he : i=j
    · subst j; simp [hd]
    · have hj : j.val < i.val := by
        have hne : i.val ≠ j.val := fun h => he (Fin.ext h)
        omega
      simp [Matrix.sub_apply, Matrix.one_apply, he, hg i j hj]
  · intro hg
    refine ⟨?_,?_⟩
    · intro i j hij
      have he : i≠j := fun h => by subst j; omega
      have h := hg i j (by omega)
      simpa [Matrix.sub_apply, Matrix.one_apply, he] using h
    · intro i
      have h := hg i i (by omega)
      exact sub_eq_zero.mp (by simpa [Matrix.sub_apply, Matrix.one_apply] using h)

variable {ι : RingAut F}

theorem mem_positiveU_iff (g : specialUnitary n ι) :
    g ∈ positiveU n ι ↔ LayerDepth 1 (g.val.val-1) :=
  unitriangular_iff_depth g.val

theorem positiveU_map_subtype :
    (positiveU n ι).map (specialUnitary n ι).subtype = unitaryUpper ι := by
  ext g
  constructor
  · rintro ⟨h,hh,rfl⟩
    exact ⟨(unitriangular_iff_depth h.val).mp hh,h.prop⟩
  · rintro ⟨hg,hs⟩
    exact ⟨⟨g,hs⟩,(unitriangular_iff_depth g).mpr hg,rfl⟩

/-- P-group recognition reuses the accepted actual SLn theorem by injection. -/
theorem positiveU_isPGroup [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (n : ℕ) (ι : RingAut F) : IsPGroup p (positiveU n ι) :=
  (SLnSylow.Uplus_isPGroup (F := F) p n).comap_subtype

end NikolovSegal.UnitarySylow
