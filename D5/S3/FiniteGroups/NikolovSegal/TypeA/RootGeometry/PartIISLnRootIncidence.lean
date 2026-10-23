/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnRootIncidence
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnRootIncidence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIIPSLnRootPermutation
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnRootAction
open Matrix
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

/-- The actual A2 multiplication incidence in any ambient rank. -/
theorem transvection_commutator_chain {i j k : Fin n} (hij : i < j) (hjk : j < k) (t s : F) :
    SpecialLinearGroup.transvection (ne_of_lt hij) t *
      SpecialLinearGroup.transvection (ne_of_lt hjk) s *
      (SpecialLinearGroup.transvection (ne_of_lt hij) t)⁻¹ *
      (SpecialLinearGroup.transvection (ne_of_lt hjk) s)⁻¹ =
      SpecialLinearGroup.transvection (ne_of_lt (hij.trans hjk)) (t*s) := by
  rw [SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change (1+Matrix.single i j t)*(1+Matrix.single j k s)*
    (1+Matrix.single i j (-t))*(1+Matrix.single j k (-s)) = 1+Matrix.single i k (t*s)
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.single_mul_single_of_ne,
    (ne_of_lt hij).symm, (ne_of_lt hjk).symm, (ne_of_lt (hij.trans hjk)).symm,
    ← Matrix.single_neg, mul_neg, neg_mul]
  <;> abel

theorem roots_commute_of_not_glued (r s : PositiveIndex n)
    (h1 : r.val.2 ≠ s.val.1) (h2 : s.val.2 ≠ r.val.1) (t u : F) :
    root r t * root s u = root s u * root r t := by
  apply Subtype.ext
  change (1+Matrix.single r.val.1 r.val.2 t)*(1+Matrix.single s.val.1 s.val.2 u) =
    (1+Matrix.single s.val.1 s.val.2 u)*(1+Matrix.single r.val.1 r.val.2 t)
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.single_mul_single_of_ne, h1, h2,
    add_comm, add_left_comm, add_assoc]

theorem root_nonzero_eq_index (r s : PositiveIndex n) (t u : F) (ht : t ≠ 0)
    (he : root r t = root s u) : r = s := by
  classical
  by_contra hne
  have hp : ¬(s.val.1=r.val.1 ∧ s.val.2=r.val.2) := by
    rintro ⟨hi,hj⟩
    exact hne (Subtype.ext (Prod.ext hi hj)).symm
  have hc := congrArg (fun g : G => g.val r.val.1 r.val.2) he
  apply ht
  simpa [root, SpecialLinearGroup.transvection_coe, ne_of_lt r.property, hp] using hc

/-- Actual commutator incidence forces scalar multiplication, with the
sign determined by the two possible orders of the image root endpoints. -/
theorem root_coordinate_triangle (a b c : PositiveIndex n) (f g h : F ≃+ F)
    (hc : ∀ t u, root a (f t)*root b (g u)*(root a (f t))⁻¹*(root b (g u))⁻¹ = root c (h (t*u))) :
    ∃ e : F, e ≠ 0 ∧ ∀ t u, h (t*u) = e*f t*g u := by
  classical
  have hf : f 1 ≠ 0 := fun he => one_ne_zero (f.map_eq_zero_iff.mp he)
  have hg : g 1 ≠ 0 := fun he => one_ne_zero (g.map_eq_zero_iff.mp he)
  have hh : h 1 ≠ 0 := fun he => one_ne_zero (h.map_eq_zero_iff.mp he)
  by_cases h1 : a.val.2 = b.val.1
  · let d : PositiveIndex n := ⟨(a.val.1,b.val.2),a.property.trans (h1.symm ▸ b.property)⟩
    have hchain : ∀ t u, root a (f t)*root b (g u)*(root a (f t))⁻¹*(root b (g u))⁻¹ = root d (f t*g u) := by
      intro t u
      cases a with
      | mk ap ha =>
        rcases ap with ⟨i,j⟩
        cases b with
        | mk bp hb =>
          rcases bp with ⟨k,l⟩
          change j=k at h1
          subst k
          exact transvection_commutator_chain ha hb (f t) (g u)
    have hd : d = c := root_nonzero_eq_index d c _ _ (mul_ne_zero hf hg)
      ((hchain 1 1).symm.trans (by simpa using hc 1 1))
    refine ⟨1,one_ne_zero,?_⟩
    intro t u
    have he := (hchain t u).symm.trans (hc t u)
    rw [hd] at he
    simpa only [one_mul] using (root_injective c he).symm
  · by_cases h2 : b.val.2 = a.val.1
    · let d : PositiveIndex n := ⟨(b.val.1,a.val.2),b.property.trans (h2.symm ▸ a.property)⟩
      have hchain : ∀ t u, root a (f t)*root b (g u)*(root a (f t))⁻¹*(root b (g u))⁻¹ = root d (-(g u*f t)) := by
        intro t u
        have he : root b (g u)*root a (f t)*(root b (g u))⁻¹*(root a (f t))⁻¹ = root d (g u*f t) := by
          cases b with
          | mk bp hb =>
            rcases bp with ⟨i,j⟩
            cases a with
            | mk ap ha =>
              rcases ap with ⟨k,l⟩
              change j=k at h2
              subst k
              exact transvection_commutator_chain hb ha (g u) (f t)
        have hi : root a (f t)*root b (g u)*(root a (f t))⁻¹*(root b (g u))⁻¹ =
            (root b (g u)*root a (f t)*(root b (g u))⁻¹*(root a (f t))⁻¹)⁻¹ := by
          simp only [_root_.mul_inv_rev, inv_inv]
          simp only [mul_assoc]
        rw [hi,he]
        exact SpecialLinearGroup.transvection_inv _ _
      have hd : d = c := root_nonzero_eq_index d c _ _ (neg_ne_zero.mpr (mul_ne_zero hg hf))
        ((hchain 1 1).symm.trans (by simpa using hc 1 1))
      refine ⟨-1,neg_ne_zero.mpr one_ne_zero,?_⟩
      intro t u
      have he := (hchain t u).symm.trans (hc t u)
      rw [hd] at he
      have hv := (root_injective c he).symm
      simpa [mul_comm] using hv
    · have he := roots_commute_of_not_glued a b h1 h2 (f 1) (g 1)
      have hz : root c (h 1) = root c 0 := by
        have hcomm := hc 1 1
        rw [he] at hcomm
        simpa [root, mul_assoc] using hcomm.symm
      exact (hh (root_injective c hz)).elim

end NikolovSegal.SLnRootAction
