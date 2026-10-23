/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnOppositeRelations
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnOppositeRelations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnOppositeRigidity
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnFullGroup
open Matrix NikolovSegal.SLnRootAction NikolovSegal.SLnNormalizer
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

abbrev negativeRoot (r : PositiveIndex n) (t : F) : G :=
  SpecialLinearGroup.transvection (ne_of_lt r.property).symm t

theorem transvections_commute {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (t s : F) :
    SpecialLinearGroup.transvection hij t * SpecialLinearGroup.transvection hkl s =
    SpecialLinearGroup.transvection hkl s * SpecialLinearGroup.transvection hij t := by
  apply Subtype.ext
  change (1+Matrix.single i j t)*(1+Matrix.single k l s) =
    (1+Matrix.single k l s)*(1+Matrix.single i j t)
  simp [Matrix.mul_add,Matrix.add_mul,Matrix.single_mul_single_of_ne,hjk,hli,
    add_comm,add_left_comm,add_assoc]

/-- Actual A2 conjugation, without ordering assumptions on the three indices. -/
theorem transvection_conjugate_chain {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (t s : F) :
    SpecialLinearGroup.transvection hij t * SpecialLinearGroup.transvection hjk s *
      (SpecialLinearGroup.transvection hij t)⁻¹ =
    SpecialLinearGroup.transvection hjk s * SpecialLinearGroup.transvection hik (t*s) := by
  rw [SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change (1+Matrix.single i j t)*(1+Matrix.single j k s)*(1+Matrix.single i j (-t)) =
    (1+Matrix.single j k s)*(1+Matrix.single i k (t*s))
  simp [Matrix.mul_add,Matrix.add_mul,Matrix.single_mul_single_of_ne,
    hij.symm,hjk.symm,hik.symm,← Matrix.single_neg,mul_neg,neg_mul]
  <;> abel

theorem transvection_conjugate_chain_right {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (t s : F) :
    SpecialLinearGroup.transvection hjk t * SpecialLinearGroup.transvection hij s *
      (SpecialLinearGroup.transvection hjk t)⁻¹ =
    SpecialLinearGroup.transvection hij s * SpecialLinearGroup.transvection hik (-s*t) := by
  rw [SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change (1+Matrix.single j k t)*(1+Matrix.single i j s)*(1+Matrix.single j k (-t)) =
    (1+Matrix.single i j s)*(1+Matrix.single i k (-s*t))
  simp [Matrix.mul_add,Matrix.add_mul,Matrix.single_mul_single_of_ne,
    hij.symm,hjk.symm,hik.symm,← Matrix.single_neg,mul_neg,neg_mul]
  <;> abel

/-- Every positive root other than the matching simple root stays in actual U
under conjugation by the opposite simple root. -/
theorem negative_simple_conjugate_mem_U (r s : PositiveIndex n)
    (hsimple : r.val.2.val=r.val.1.val+1) (hsr : s ≠ r) (t u : F) :
    negativeRoot r t * root s u * (negativeRoot r t)⁻¹ ∈ Uplus n F := by
  let i := r.val.1
  let j := r.val.2
  let a := s.val.1
  let b := s.val.2
  by_cases hai : a=i
  · have hbj : b ≠ j := by
      intro hbj; exact hsr (Subtype.ext (Prod.ext hai hbj))
    have hjb : j < b := by
      change j.val < b.val
      have hs := s.property
      change a.val < b.val at hs
      have hbv : b.val ≠ j.val := fun h => hbj (Fin.ext h)
      change j.val=i.val+1 at hsimple
      rw [hai] at hs
      omega
    have hib : i < b := by simpa only [← hai] using s.property
    have he := transvection_conjugate_chain (ne_of_lt r.property).symm
      (ne_of_lt hib) (ne_of_lt hjb) t u
    have hx : root s u = SpecialLinearGroup.transvection (ne_of_lt hib) u := by
      apply Subtype.ext
      change 1+Matrix.single s.val.1 s.val.2 u = 1+Matrix.single i b u
      rw [show s.val.1=i from hai]
    rw [hx]
    change SpecialLinearGroup.transvection (ne_of_lt r.property).symm t *
      SpecialLinearGroup.transvection (ne_of_lt hib) u *
      (SpecialLinearGroup.transvection (ne_of_lt r.property).symm t)⁻¹ ∈ Uplus n F
    rw [he]
    exact (Uplus n F).mul_mem (transvection_mem_Uplus hib u) (transvection_mem_Uplus hjb (t*u))
  · by_cases hbj : b=j
    · have hai' : a < i := by
        change a.val < i.val
        have hs := s.property
        change a.val < b.val at hs
        have hav : a.val ≠ i.val := fun h => hai (Fin.ext h)
        change j.val=i.val+1 at hsimple
        rw [hbj] at hs
        omega
      have haj : a < j := lt_trans hai' r.property
      have he := transvection_conjugate_chain_right (ne_of_lt haj)
        (ne_of_lt r.property).symm (ne_of_lt hai') t u
      have hx : root s u = SpecialLinearGroup.transvection (ne_of_lt haj) u := by
        apply Subtype.ext
        change 1+Matrix.single s.val.1 s.val.2 u = 1+Matrix.single a j u
        rw [show s.val.2=j from hbj]
      rw [hx]
      change SpecialLinearGroup.transvection (ne_of_lt r.property).symm t *
        SpecialLinearGroup.transvection (ne_of_lt haj) u *
        (SpecialLinearGroup.transvection (ne_of_lt r.property).symm t)⁻¹ ∈ Uplus n F
      rw [he]
      exact (Uplus n F).mul_mem (transvection_mem_Uplus haj u) (transvection_mem_Uplus hai' (-u*t))
    · have he := transvections_commute (ne_of_lt r.property).symm
        (ne_of_lt s.property) (Ne.symm hai) hbj t u
      have hc : negativeRoot r t * root s u * (negativeRoot r t)⁻¹ = root s u := by
        change SpecialLinearGroup.transvection (ne_of_lt r.property).symm t *
          SpecialLinearGroup.transvection (ne_of_lt s.property) u *
          (SpecialLinearGroup.transvection (ne_of_lt r.property).symm t)⁻¹ = _
        rw [he]; simp [mul_assoc,root]
      rw [hc]
      exact root_mem_Uplus s u

/-- The genuine opposite root centralizes its actual diagonal-character kernel. -/
theorem negativeRoot_commutes_kernel (r : PositiveIndex n) (t : F)
    (d : G) (hd : d ∈ torusKernel (F := F) r) : d*negativeRoot r t=negativeRoot r t*d := by
  apply (diagonal_commutes_iff d _ ((mem_torusKernel_iff r d).mp hd).1).mpr
  intro a b
  have hdij := ((mem_torusKernel_iff r d).mp hd).2
  by_cases hab : a=b
  · subst b; simp
  by_cases hp : r.val.2=a ∧ r.val.1=b
  · rcases hp with ⟨rfl,rfl⟩; rw [hdij]; simp
  · simp [negativeRoot,SpecialLinearGroup.transvection_coe,Matrix.one_apply,Matrix.single_apply,hab,hp]
end NikolovSegal.SLnFullGroup
