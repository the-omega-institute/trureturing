/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRootOperations
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRootOperations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitarySylowFlag
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryInnerUNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual unitary root operations for whole-group elimination.
All matrices belong to the immutable literal Steinberg-fixed SL carrier.
The paired roots are used in both orientations; no SL-to-SU inference is made. -/
namespace NikolovSegal.UnitaryWholeGroupWidth
open Matrix UnitarySylow SLnNormalizer PartIIUnitaryUpperTorus PartIIUnitriangularLayers
universe u
variable {F : Type u} [Field F] {n : ℕ} {ι : RingAut F}

abbrev Positive (g : specialUnitary n ι) : Prop := LayerDepth 1 (g.val.val-1)
def Negative (g : specialUnitary n ι) : Prop :=
  ∀ r c : Fin n, r.val < c.val+1 → (g.val.val-1) r c=0

@[simp] theorem positive_one : Positive (1 : specialUnitary n ι) := by
  intro r c h; simp
@[simp] theorem negative_one : Negative (1 : specialUnitary n ι) := by
  intro r c h; simp

def pairRoot (ι : RingAut F) (hinv : Function.Involutive ι)
    {i j : Fin n} (hij : i≠j) (hi : i≠i.rev) (hj : j≠j.rev) (t : F) :
    specialUnitary n ι :=
  ⟨SpecialLinearGroup.transvection hij t *
    SpecialLinearGroup.transvection (Fin.rev_injective.ne hij.symm) (-ι t), by
      change steinberg ι _ = _
      rw [map_mul,steinberg_transvection,steinberg_transvection]
      simp only [Fin.rev_rev,map_neg,hinv t,neg_neg]
      exact transvections_commute _ _ hi.symm hj _ _⟩

theorem pairRoot_matrix (hinv : Function.Involutive ι)
    {i j : Fin n} (hij : i≠j) (hi : i≠i.rev) (hj : j≠j.rev) (t : F) :
    (pairRoot ι hinv hij hi hj t).val.val =
      1 + single i j t + single j.rev i.rev (-ι t) :=
  paired_root_matrix hij hj t (-ι t)

theorem pairRoot_positive (hinv : Function.Involutive ι)
    {i j : Fin n} (hij : i≠j) (hi : i≠i.rev) (hj : j≠j.rev)
    (hlt : i.val < j.val) (t : F) : Positive (pairRoot ι hinv hij hi hj t) := by
  apply (mem_positiveU_iff _).mp
  change _ ∈ Uplus n F
  apply (Uplus n F).mul_mem
  · exact transvection_mem_Uplus hlt t
  · apply transvection_mem_Uplus (b := -ι t)
    simp only [Fin.val_rev]
    omega

theorem pairRoot_negative (hinv : Function.Involutive ι)
    {i j : Fin n} (hij : i≠j) (hi : i≠i.rev) (hj : j≠j.rev)
    (hlt : j.val < i.val) (t : F) : Negative (pairRoot ι hinv hij hi hj t) := by
  intro r c hrc
  rw [pairRoot_matrix]
  have h₁ : ¬(i=r ∧ j=c) := by rintro ⟨rfl,rfl⟩; omega
  have h₂ : ¬(j.rev=r ∧ i.rev=c) := by
    rintro ⟨rfl,rfl⟩
    simp only [Fin.val_rev] at hrc
    omega
  simp [Matrix.sub_apply,Matrix.add_apply,Matrix.single_apply,h₁,h₂]

/-- Exact row operation for the two simultaneous actual unitary transvections. -/
theorem mul_pairRoot_entry (hinv : Function.Involutive ι)
    {i j : Fin n} (hij : i≠j) (hi : i≠i.rev) (hj : j≠j.rev)
    (t : F) (g : specialUnitary n ι) (r c : Fin n) :
    (g * pairRoot ι hinv hij hi hj t).val.val r c =
      g.val.val r c + (if c=j then g.val.val r i*t else 0) +
        (if c=i.rev then g.val.val r j.rev*(-ι t) else 0) := by
  change (g.val.val * (pairRoot ι hinv hij hi hj t).val.val) r c = _
  rw [pairRoot_matrix,Matrix.mul_add,Matrix.mul_add,Matrix.mul_one]
  simp only [Matrix.add_apply]
  congr 1
  · by_cases h : c=j <;> simp [h]
  · by_cases h : c=i.rev <;> simp [h]

/-- Literal last-row isotropy, derived from actual fixedness and the group inverse. -/
theorem row_isotropic (hinv : Function.Involutive ι) (g : specialUnitary n ι)
    (r : Fin n) (hr : r≠r.rev) :
    (∑ t : Fin n, g.val.val r t * ι (g.val.val r t.rev))=0 := by
  have hi : ∀ t, (g.val⁻¹).val t r.rev = ι (g.val.val r t.rev) := by
    intro t
    have hh := congrArg (fun A : SpecialLinearGroup (Fin n) F => ι (A r t.rev)) g.prop
    rw [steinberg_entry,Fin.rev_rev] at hh
    rw [hinv] at hh
    exact hh
  have he := congrArg (fun A : SpecialLinearGroup (Fin n) F => A r r.rev)
    (mul_inv_cancel g.val)
  simpa only [SpecialLinearGroup.coe_mul,Matrix.mul_apply,hi,
    SpecialLinearGroup.coe_one,Matrix.one_apply,if_neg hr] using he

end NikolovSegal.UnitaryWholeGroupWidth
