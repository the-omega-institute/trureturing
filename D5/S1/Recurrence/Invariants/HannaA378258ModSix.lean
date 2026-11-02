/- GID: D5/S1/Recurrence/Invariants/HannaA378258ModSix
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaA378258ModSix
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Modulo-three reflection and dyadic parity exclude Hanna's two residues. -/

import D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaA378258ModSix
open PowerSeries

/-- Hanna's separate modulo-six conjecture, with existence and all normalized solutions. -/
def claim : Prop :=
  (∃ A, HannaA378258SquareRootParity.IsGF A) ∧
    ∀ A, HannaA378258SquareRootParity.IsGF A → ∀ n : ℕ, 1 < n →
      ∃ z : ℤ, coeff n A = z ∧ z % 6 ≠ 1 ∧ z % 6 ≠ 5

private theorem plus_minus_unique {R : Type*} [CommRing R] [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0) {f g : PowerSeries R}
    (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1)
    (hf : (f + f ^ 2).subst (f - f ^ 2) = X)
    (hg : (g + g ^ 2).subst (g - g ^ 2) = X) : f = g := by
  have vf0 : constantCoeff (f + f ^ 2) = 0 := by simp [hf0]
  have vg0 : constantCoeff (g + g ^ 2) = 0 := by simp [hg0]
  have vf1 : coeff 1 (f + f ^ 2) = 1 := by simp [coeff_one_pow, hf0, hf1]
  have vg1 : coeff 1 (g + g ^ 2) = 1 := by simp [coeff_one_pow, hg0, hg1]
  have uf : HasSubst (f - f ^ 2) := .of_constantCoeff_zero (by simp [hf0])
  have ug : HasSubst (g - g ^ 2) := .of_constantCoeff_zero (by simp [hg0])
  have vf : HasSubst (f + f ^ 2) := .of_constantCoeff_zero vf0
  have vg : HasSubst (g + g ^ 2) := .of_constantCoeff_zero vg0
  have ef := subst_eq_X_of_subst_eq_X (f + f ^ 2) vf0 (vf1 ▸ isUnit_one) uf hf
  have eg := subst_eq_X_of_subst_eq_X (g + g ^ 2) vg0 (vg1 ▸ isUnit_one) ug hg
  rw [subst_sub vf, subst_pow vf] at ef
  rw [subst_sub vg, subst_pow vg] at eg
  have hu : IsUnit (1 - f.subst (f + f ^ 2) - g.subst (g + g ^ 2)) := by
    apply isUnit_iff_constantCoeff.mpr
    simp [constantCoeff_subst_eq_zero vf0 f hf0, constantCoeff_subst_eq_zero vg0 g hg0]
  have he : f.subst (f + f ^ 2) = g.subst (g + g ^ 2) := by
    apply sub_eq_zero.mp
    apply hu.mul_left_cancel
    linear_combination ef - eg
  have hs : (f + f ^ 2).subst (f + f ^ 2) = (g + g ^ 2).subst (g + g ^ 2) := by
    simp only [subst_add vf, subst_pow vf, subst_add vg, subst_pow vg, he]
  have hv := HannaHalfIterateCubicModThree.half_unique h2 vf0 vg0 vf1 vg1 hs rfl
  have hu' : IsUnit (1 + f + g) := by
    apply isUnit_iff_constantCoeff.mpr
    simp [hf0, hg0]
  apply sub_eq_zero.mp
  apply hu'.mul_left_cancel
  linear_combination hv

private theorem plus_minus_odd {R : Type*} [CommRing R] [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0) (f : PowerSeries R)
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1)
    (hf : (f + f ^ 2).subst (f - f ^ 2) = X) :
    f = -(f.subst (-X)) := by
  have hn : HasSubst (-X : PowerSeries R) := .of_constantCoeff_zero (by simp)
  let g := -(f.subst (-X))
  have hg0 : constantCoeff g = 0 := by
    simp [g, constantCoeff_subst_eq_zero (by simp : constantCoeff (-X : PowerSeries R) = 0) f hf0]
  have hg1 : coeff 1 g = 1 := by
    have he := congrArg (coeff 1) (rescale_eq_subst (-1 : R) f)
    simpa [g, coeff_rescale, hf1] using congrArg Neg.neg he.symm
  have hv0 : constantCoeff (f + f ^ 2) = 0 := by simp [hf0]
  have hv1 : coeff 1 (f + f ^ 2) = 1 := by simp [coeff_one_pow, hf0, hf1]
  have hu : HasSubst (f - f ^ 2) := .of_constantCoeff_zero (by simp [hf0])
  have hf' := subst_eq_X_of_subst_eq_X (f + f ^ 2) hv0 (hv1 ▸ isUnit_one) hu hf
  have hga : g + g ^ 2 = -((f - f ^ 2).subst (-X)) := by
    dsimp [g]
    rw [subst_sub hn, subst_pow hn]
    ring
  have hgb : g - g ^ 2 = -((f + f ^ 2).subst (-X)) := by
    dsimp [g]
    rw [subst_add hn, subst_pow hn]
    ring
  have hb : HasSubst (-((f + f ^ 2).subst (-X))) :=
    .of_constantCoeff_zero (by simpa only [← hgb] using (show constantCoeff (g - g ^ 2) = 0 by simp [hg0]))
  apply plus_minus_unique h2 hf0 hg0 hf1 hg1 hf
  rw [hga, hgb, subst_neg hb, subst_comp_subst_apply hn hb]
  simp only [subst_neg hb, subst_X hb, neg_neg]
  rw [← subst_comp_subst_apply (.of_constantCoeff_zero hv0) hn, hf']
  simp

end D5.S1.Recurrence.Invariants.HannaA378258ModSix
