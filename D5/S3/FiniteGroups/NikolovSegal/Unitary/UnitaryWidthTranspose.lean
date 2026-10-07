/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthTranspose
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthTranspose
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthRootOperations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NikolovSegal.UnitaryWholeGroupWidth
open Matrix UnitarySylow PartIIUnitaryUpperTorus
universe u
variable {F : Type u} [Field F] {n : ℕ} {ι : RingAut F}

/-- Transposition really stays inside the same actual SU carrier. -/
def transpose (g : specialUnitary n ι) : specialUnitary n ι :=
  ⟨g.val.transpose,by
    apply SpecialLinearGroup.ext
    intro i j
    rw [steinberg_entry]
    change ι (Matrix.adjugate g.val.val.transpose j.rev i.rev)=g.val.val j i
    rw [← Matrix.adjugate_transpose]
    exact congrArg (fun A : SpecialLinearGroup (Fin n) F => A j i) g.prop⟩

@[simp] theorem transpose_entry (g : specialUnitary n ι) (i j : Fin n) :
    (transpose g).val.val i j=g.val.val j i := rfl

@[simp] theorem transpose_transpose (g : specialUnitary n ι) : transpose (transpose g)=g := by
  apply Subtype.ext; apply SpecialLinearGroup.ext; intro i j; rfl

theorem transpose_mul (g h : specialUnitary n ι) : transpose (g*h)=transpose h*transpose g := by
  apply Subtype.ext; apply Subtype.ext
  exact Matrix.transpose_mul _ _

theorem transpose_inv (g : specialUnitary n ι) : transpose g⁻¹=(transpose g)⁻¹ := by
  apply Subtype.ext; apply Subtype.ext
  exact Matrix.adjugate_transpose _

theorem positive_transpose_iff (g : specialUnitary n ι) : Positive (transpose g) ↔ Negative g := by
  constructor <;> intro h r c hrc <;>
    simpa only [Matrix.sub_apply,Matrix.one_apply,eq_comm,transpose_entry] using h c r hrc

theorem positive_inv {g : specialUnitary n ι} (hg : Positive g) : Positive g⁻¹ := by
  exact (mem_positiveU_iff _).mp ((positiveU n ι).inv_mem ((mem_positiveU_iff _).mpr hg))

theorem negative_inv {g : specialUnitary n ι} (hg : Negative g) : Negative g⁻¹ := by
  apply (positive_transpose_iff _).mp
  rw [transpose_inv]
  exact positive_inv ((positive_transpose_iff _).mpr hg)

theorem positive_mul {g h : specialUnitary n ι} (hg : Positive g) (hh : Positive h) :
    Positive (g*h) :=
  (mem_positiveU_iff _).mp ((positiveU n ι).mul_mem
    ((mem_positiveU_iff _).mpr hg) ((mem_positiveU_iff _).mpr hh))

theorem negative_mul {g h : specialUnitary n ι} (hg : Negative g) (hh : Negative h) :
    Negative (g*h) := by
  apply (positive_transpose_iff _).mp
  rw [transpose_mul]
  exact positive_mul ((positive_transpose_iff _).mpr hh) ((positive_transpose_iff _).mpr hg)

end NikolovSegal.UnitaryWholeGroupWidth
