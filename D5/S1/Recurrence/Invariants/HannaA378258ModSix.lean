/- GID: D5/S1/Recurrence/Invariants/HannaA378258ModSix
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaA378258ModSix
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Modulo-three reflection and dyadic parity exclude Hanna's two residues. -/

/-
admission_basis: open-problem-resolution (#25601; Proved).
All new declarations have proof_shape: bind-only and escape_witness: none.
claim is consumed by result. plus_minus_unique is consumed by plus_minus_odd;
plus_minus_odd is consumed by integral_even_three; integral_even_three is consumed
by result. The external preregistered settlement supplies admission for result.
The original IsGF, existence, integrality and parity are reused without alteration.
Mathlib compositional-inverse uniqueness and the frozen half_unique supply uniqueness;
no square-root or Catalan coefficient proof is repeated.
-/

import D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity

/-! # Hanna's modulo-six conjecture -/

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
  have uf0 : constantCoeff (f - f ^ 2) = 0 := by simp [hf0]
  have uf : HasSubst (f - f ^ 2) := .of_constantCoeff_zero uf0
  have ug0 : constantCoeff (g - g ^ 2) = 0 := by simp [hg0]
  have ug : HasSubst (g - g ^ 2) := .of_constantCoeff_zero ug0
  have vf : HasSubst (f + f ^ 2) := .of_constantCoeff_zero vf0
  have vg : HasSubst (g + g ^ 2) := .of_constantCoeff_zero vg0
  have ef := subst_eq_X_of_subst_eq_X (f + f ^ 2) vf0 (vf1 ▸ isUnit_one) uf hf
  have eg := subst_eq_X_of_subst_eq_X (g + g ^ 2) vg0 (vg1 ▸ isUnit_one) ug hg
  rw [subst_sub vf, subst_pow vf] at ef
  rw [subst_sub vg, subst_pow vg] at eg
  have hcf : constantCoeff (f.subst (f + f ^ 2)) = 0 :=
    constantCoeff_subst_eq_zero vf0 f hf0
  have hcg : constantCoeff (g.subst (g + g ^ 2)) = 0 :=
    constantCoeff_subst_eq_zero vg0 g hg0
  have hp0 : constantCoeff (X - X ^ 2 : PowerSeries R) = 0 := by simp
  have hp1 : IsUnit (coeff 1 (X - X ^ 2 : PowerSeries R)) := by simp [coeff_X]
  have hpf : (X - X ^ 2 : PowerSeries R).subst (f.subst (f + f ^ 2)) = X := by
    rw [subst_sub (.of_constantCoeff_zero hcf), subst_X (.of_constantCoeff_zero hcf),
      subst_pow (.of_constantCoeff_zero hcf), subst_X (.of_constantCoeff_zero hcf)]
    exact ef
  have hpg : (X - X ^ 2 : PowerSeries R).subst (g.subst (g + g ^ 2)) = X := by
    rw [subst_sub (.of_constantCoeff_zero hcg), subst_X (.of_constantCoeff_zero hcg),
      subst_pow (.of_constantCoeff_zero hcg), subst_X (.of_constantCoeff_zero hcg)]
    exact eg
  have he : f.subst (f + f ^ 2) = g.subst (g + g ^ 2) :=
    (eq_substInvOfIsUnit_of_subst_eq_X _ hp0 hp1 (.of_constantCoeff_zero hcf) hpf).trans
      (eq_substInvOfIsUnit_of_subst_eq_X _ hp0 hp1 (.of_constantCoeff_zero hcg) hpg).symm
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
    f = -(f.subst (-X : PowerSeries R)) := by
  have hn0 : constantCoeff (-X : PowerSeries R) = 0 := by simp
  have hn : HasSubst (-X : PowerSeries R) := .of_constantCoeff_zero hn0
  let g : PowerSeries R := -(f.subst (-X : PowerSeries R))
  have hg0 : constantCoeff g = 0 := by
    have hc : constantCoeff (f.subst (-X : PowerSeries R)) = 0 :=
      constantCoeff_subst_eq_zero hn0 f hf0
    simp only [g, map_neg, hc, neg_zero]
  have hg1 : coeff 1 g = 1 := by
    have he := congrArg (coeff 1) (rescale_eq_subst (-1 : R) f)
    simpa [g, coeff_rescale, hf1] using congrArg Neg.neg he.symm
  have hv0 : constantCoeff (f + f ^ 2) = 0 := by simp [hf0]
  have hv1 : coeff 1 (f + f ^ 2) = 1 := by simp [coeff_one_pow, hf0, hf1]
  have hu0 : constantCoeff (f - f ^ 2) = 0 := by simp [hf0]
  have hu : HasSubst (f - f ^ 2) := .of_constantCoeff_zero hu0
  have hf' := subst_eq_X_of_subst_eq_X (f + f ^ 2) hv0 (hv1 ▸ isUnit_one) hu hf
  have hga : g + g ^ 2 = -((f - f ^ 2).subst (-X : PowerSeries R)) := by
    dsimp [g]
    rw [subst_sub hn, subst_pow hn]
    ring
  have hgb : g - g ^ 2 = -((f + f ^ 2).subst (-X : PowerSeries R)) := by
    dsimp [g]
    rw [subst_add hn, subst_pow hn]
    ring
  have hb0 : constantCoeff (-((f + f ^ 2).subst (-X : PowerSeries R))) = 0 := by
    rw [← hgb]
    simp [hg0]
  have hb : HasSubst (-((f + f ^ 2).subst (-X : PowerSeries R))) :=
    .of_constantCoeff_zero hb0
  have hneg (u : PowerSeries R) (hu : HasSubst u) (v : PowerSeries R) :
      (-v).subst u = -(v.subst u) := by
    simpa only [coe_substAlgHom] using map_neg (substAlgHom hu) v
  apply plus_minus_unique h2 hf0 hg0 hf1 hg1 hf
  rw [hga, hgb, hneg _ hb _, subst_comp_subst_apply hn hb]
  rw [hneg _ hb _, subst_X hb, neg_neg]
  rw [← subst_comp_subst_apply (.of_constantCoeff_zero hv0) hn, hf']
  rw [subst_X hn, neg_neg]


private theorem integral_even_three (f : PowerSeries ℤ)
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1)
    (hf : (f - 5 * f ^ 2).subst (f - f ^ 2) = X)
    (n : ℕ) (hn : Even n) : 3 ∣ coeff n f := by
  let hom := Int.castRingHom (ZMod 3)
  let g := f.map hom
  have hg0 : constantCoeff g = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp [g, coeff_map, coeff_zero_eq_constantCoeff, hf0]
  have hg1 : coeff 1 g = 1 := by simp [g, coeff_map, hf1]
  have harg : constantCoeff (f - f ^ 2) = 0 := by simp [hf0]
  have he := congrArg (PowerSeries.map hom) hf
  have hm : PowerSeries.map hom ((f - 5 * f ^ 2).subst (f - f ^ 2)) =
      ((f - 5 * f ^ 2).map hom).subst ((f - f ^ 2).map hom) :=
    map_subst (.of_constantCoeff_zero harg) _
  rw [hm] at he
  have h5 : (5 : PowerSeries (ZMod 3)) = -1 := by
    calc
      (5 : PowerSeries (ZMod 3)) = C (5 : ZMod 3) := (map_ofNat _ 5).symm
      _ = -1 := by rw [show (5 : ZMod 3) = -1 by decide]; simp
  have hg : (g + g ^ 2).subst (g - g ^ 2) = X := by
    simpa [g, map_sub, map_mul, map_pow, map_ofNat, h5] using he
  have hs := plus_minus_odd (by decide : (2 : ZMod 3) ≠ 0) g hg0 hg1 hg
  have hr : rescale (-1 : ZMod 3) g = g.subst (-X) := by
    simpa using rescale_eq_subst (-1 : ZMod 3) g
  have hc := congrArg (coeff n) hs
  rw [map_neg, ← hr, coeff_rescale, hn.neg_one_pow, one_mul] at hc
  have hz : coeff n g = 0 := by
    have ht : (2 : ZMod 3) * coeff n g = 0 := by linear_combination hc
    exact (mul_eq_zero.mp ht).resolve_left (by decide)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (coeff n f) 3).mp
    (by simpa [g, coeff_map, hom] using hz)

theorem result : claim := by
  refine ⟨HannaA378258SquareRootParity.result.1, ?_⟩
  intro A hA n hn
  have hi : ∀ k : ℕ, ∃ z : ℤ, coeff k A = (z : ℚ) := by
    intro k
    by_cases hk : k = 0
    · subst k
      exact ⟨0, by simpa only [coeff_zero_eq_constantCoeff, Int.cast_zero] using hA.1⟩
    · obtain ⟨z, hz, _⟩ := HannaA378258SquareRootParity.result.2 A hA k (by omega)
      exact ⟨z, hz⟩
  choose a ha using hi
  let f : PowerSeries ℤ := mk a
  have hmap : f.map (Int.castRingHom ℚ) = A := by
    ext k
    simp only [f, coeff_map, coeff_mk]
    change (a k : ℚ) = coeff k A
    exact (ha k).symm
  have hf0 : constantCoeff f = 0 := by
    have he := congrArg (coeff 0) hmap
    simp only [coeff_map, coeff_zero_eq_constantCoeff, hA.1] at he
    change ((constantCoeff f : ℤ) : ℚ) = 0 at he
    exact_mod_cast he
  have hf1 : coeff 1 f = 1 := by
    have he := congrArg (coeff 1) hmap
    simp only [coeff_map, hA.2.1] at he
    change ((coeff 1 f : ℤ) : ℚ) = 1 at he
    exact_mod_cast he
  have hf : (f - 5 * f ^ 2).subst (f - f ^ 2) = X := by
    apply PowerSeries.map_injective (Int.castRingHom ℚ) (by exact Int.cast_injective)
    have harg : constantCoeff (f - f ^ 2) = 0 := by simp [hf0]
    have hm : PowerSeries.map (Int.castRingHom ℚ) ((f - 5 * f ^ 2).subst (f - f ^ 2)) =
        ((f - 5 * f ^ 2).map (Int.castRingHom ℚ)).subst
          ((f - f ^ 2).map (Int.castRingHom ℚ)) :=
      map_subst (.of_constantCoeff_zero harg) _
    rw [hm]
    simp only [map_sub, map_mul, map_pow, map_ofNat, map_X, hmap]
    obtain ⟨B, hB, hs⟩ := hA.2.2
    have hb : A - 5 * A ^ 2 = B := by linear_combination hB
    rw [hb, hs]
  obtain ⟨z, hz, hp⟩ := HannaA378258SquareRootParity.result.2 A hA n (by omega)
  have hzcoeff : coeff n f = z := by
    have he := congrArg (coeff n) hmap
    simp only [coeff_map, hz] at he
    change ((coeff n f : ℤ) : ℚ) = (z : ℚ) at he
    exact_mod_cast he
  have hdiv : Odd z → 3 ∣ z := by
    intro ho
    obtain ⟨k, hk⟩ := hp.mp ho
    have heven : Even n := by
      cases k with
      | zero => simp at hk; omega
      | succ k =>
        rw [hk, pow_succ]
        exact (by decide : Even (2 : ℕ)).mul_left _
    simpa only [hzcoeff] using integral_even_three f hf0 hf1 hf n heven
  refine ⟨z, hz, ?_, ?_⟩
  · intro h
    have ho : Odd z := by
      rw [Int.odd_iff]
      omega
    have hd := hdiv ho
    omega
  · intro h
    have ho : Odd z := by
      rw [Int.odd_iff]
      omega
    have hd := hdiv ho
    omega

end D5.S1.Recurrence.Invariants.HannaA378258ModSix
