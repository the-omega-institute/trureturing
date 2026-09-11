/- GID: D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/CatalanCubicCompositionParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A cubic Catalan composition has odd coefficients exactly at zero and powers of two. -/

import D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity

open PowerSeries

namespace D5.S1.Recurrence.Invariants.CatalanCubicCompositionParity

noncomputable def catalanSeries : PowerSeries ℤ := mk (fun n => (catalan n : ℤ))

private theorem catalan_map :
    catalanSeries = PowerSeries.catalanSeries.map (Nat.castRingHom ℤ) := by
  ext n
  simp [catalanSeries]

theorem catalan_equation : catalanSeries = 1 + X * catalanSeries ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ))
    PowerSeries.catalanSeries_sq_mul_X_add_one
  simpa [← catalan_map, add_comm, mul_comm] using h.symm

noncomputable def generatingSeries : PowerSeries ℤ :=
  catalanSeries.subst (X * catalanSeries ^ 3)

noncomputable def a (n : ℕ) : ℤ := coeff n generatingSeries

theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    generatingSeries = 1 + (X * catalanSeries ^ 3) * generatingSeries ^ 2 := by
  have hy : constantCoeff (X * catalanSeries ^ 3) = 0 := by simp
  have hs : HasSubst (X * catalanSeries ^ 3) := .of_constantCoeff_zero hy
  have ho : (1 : PowerSeries ℤ).subst (X * catalanSeries ^ 3) = 1 := by
    rw [← coe_substAlgHom hs]
    exact map_one _
  have he : generatingSeries = 1 + (X * catalanSeries ^ 3) * generatingSeries ^ 2 := by
    have h := congrArg (fun f : PowerSeries ℤ => f.subst (X * catalanSeries ^ 3))
      catalan_equation
    simpa only [generatingSeries, subst_add hs, subst_mul hs, subst_X hs,
      subst_pow hs, ho] using h
  refine ⟨?_, he⟩
  simpa using congrArg constantCoeff he

private theorem quadratic_unique {R : Type*} [CommRing R]
    {y f g : PowerSeries R} (hy : constantCoeff y = 0)
    (hf : f = 1 + y * f ^ 2) (hg : g = 1 + y * g ^ 2) : f = g := by
  -- The difference is annihilated by a series with constant coefficient one.
  have hu : IsUnit (1 - y * (f + g)) := by
    rw [isUnit_iff_constantCoeff]
    simp [hy]
  have he : (1 - y * (f + g)) * (f - g) = (1 - y * (f + g)) * 0 := by
    linear_combination hf - hg
  exact sub_eq_zero.mp (hu.mul_left_cancel he)

theorem mod_two_identity : generatingSeries.map (Int.castRingHom (ZMod 2)) =
    1 + CatalanCompositionSquareParity.catalanSeries.map (Int.castRingHom (ZMod 2)) := by
  let hom := Int.castRingHom (ZMod 2)
  let c := catalanSeries.map hom
  let k := CatalanCompositionSquareParity.catalanSeries.map hom
  let y := X * c ^ 3
  have hk : k = X * c := by
    change (X * (PowerSeries.catalanSeries.map (Nat.castRingHom ℤ))).map hom = X * c
    simp [c, catalan_map]
  have he : k = X + k ^ 2 := by
    simpa [k, hom] using congrArg (PowerSeries.map hom)
      CatalanCompositionSquareParity.catalan_equation.2.2
  have hz : (2 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := ZMod 2)) (show (2 : ZMod 2) = 0 by decide)
  have hfactor : k * (1 + k) = X := by
    linear_combination he + k ^ 2 * hz
  -- Clear the two powers of X before using the cubic Catalan factorization.
  have hcubic : y * (1 + k) ^ 2 = k := by
    apply X_pow_mul_cancel (k := 2)
    calc
      X ^ 2 * (y * (1 + k) ^ 2) = k ^ 3 * (1 + k) ^ 2 := by
        rw [hk]
        dsimp [y]
        ring
      _ = k * (k * (1 + k)) ^ 2 := by ring
      _ = X ^ 2 * k := by rw [hfactor]; ring
  have hf : generatingSeries.map hom = 1 + y * (generatingSeries.map hom) ^ 2 := by
    simpa [y, c] using congrArg (PowerSeries.map hom) generating_equation.2
  exact quadratic_unique (by simp [y]) hf (by rw [hcubic])

theorem hanna_conjecture (n : ℕ) : Odd (a n) ↔ (n = 0 ∨ ∃ k : ℕ, n = 2 ^ k) := by
  rw [← ZMod.intCast_eq_one_iff_odd]
  have he := congrArg (coeff n) mod_two_identity
  simp only [coeff_map, map_add, coeff_one] at he
  change (a n : ZMod 2) = _ at he
  rw [he]
  by_cases hn : n = 0
  · subst n
    simp [coeff_zero_eq_constantCoeff, CatalanCompositionSquareParity.catalanSeries]
  · simp only [hn, if_false, zero_add, false_or]
    simpa only [coeff_map] using CatalanCompositionSquareParity.binary_catalan n

#print axioms catalan_equation
#print axioms generating_equation
#print axioms mod_two_identity
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.CatalanCubicCompositionParity
