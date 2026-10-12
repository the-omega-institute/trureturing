/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2Relations
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2Relations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo.PartIISLnF2Centralizer
import Mathlib.Algebra.CharP.Two

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnF2Residual
open Matrix NikolovSegal.SLnRootAction NikolovSegal.SLnFullGroup
open NikolovSegal.SLnNormalizer
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

/-- The actual rank-one braid identity at arbitrary indices. -/
theorem transvection_braid {i j : Fin n} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1:F) * SpecialLinearGroup.transvection hij.symm (-1) *
      SpecialLinearGroup.transvection hij 1 =
    SpecialLinearGroup.transvection hij.symm (-1) * SpecialLinearGroup.transvection hij 1 *
      SpecialLinearGroup.transvection hij.symm (-1) := by
  apply Subtype.ext
  change (1+Matrix.single i j (1:F))*(1+Matrix.single j i (-1))*(1+Matrix.single i j 1) =
    (1+Matrix.single j i (-1))*(1+Matrix.single i j 1)*(1+Matrix.single j i (-1))
  simp [Matrix.mul_add,Matrix.add_mul,Matrix.single_mul_single_of_ne,hij,hij.symm,
    ← Matrix.single_neg]
  <;> abel

/-- In characteristic two the opposite elementary pair has product of order
dividing three, by the genuine braid relation. -/
theorem opposite_pair_cube [CharP F 2] {i j : Fin n} (hij : i ≠ j) :
    (SpecialLinearGroup.transvection hij (1:F)*SpecialLinearGroup.transvection hij.symm 1)^3=1 := by
  let x : G := SpecialLinearGroup.transvection hij 1
  let y : G := SpecialLinearGroup.transvection hij.symm 1
  have hx : x*x=1 := by simpa only [pow_two] using transvection_pow_char 2 i j hij (1:F)
  have hy : y*y=1 := by simpa only [pow_two] using transvection_pow_char 2 j i hij.symm (1:F)
  have hb : x*y*x=y*x*y := by simpa only [CharTwo.neg_eq] using transvection_braid (F := F) hij
  change (x*y)^3=1
  calc
    _ = (x*y*x)*(y*x*y) := by simp only [pow_succ,pow_zero,one_mul]; group
    _ = (y*x*y)*(y*x*y) := by rw [hb]
    _ = y*x*(y*y)*x*y := by group
    _ = 1 := by rw [hy,mul_one,mul_assoc y x x,hx,mul_one,hy]

/-- The two-element field has trivial actual SL centre. This is a matrix
statement and supplies a proved projective isomorphism, not an automorphism lift. -/
theorem center_eq_one [Fintype F] (hF : Fintype.card F=2) (hn : 0 < n)
    (z : G) (hz : z ∈ Subgroup.center G) : z=1 := by
  let i : Fin n := ⟨0,hn⟩
  letI : Nonempty (Fin n) := ⟨i⟩
  have hs := SpecialLinearGroup.scalar_eq_self_of_mem_center hz i
  have hne : z.val i i ≠ 0 := by
    intro he
    have hz0 : z.val=0 := by rw [← hs,he]; simp
    have hd := z.property
    rw [hz0,Matrix.det_zero] at hd
    exact zero_ne_one hd
  have he := (eq_zero_or_one hF (z.val i i)).resolve_left hne
  apply Subtype.ext
  rw [← hs,he]
  simp

end NikolovSegal.SLnF2Residual
