/- GID: D5/S3/VertexAlgebra/Lattice/LeechFrame/NormFourMixedProducts
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LeechFrame/NormFourMixedProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Vanishing singular mixed products of norm-four lattice Virasoro states. -/

import D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector
import Batteries.Tactic.OpenPrivate

/-! Singular mixed products of the norm-four lattice states used in the Leech frame. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open private ground currentMode currentMode_single currentMode_ground partial_quadratic
  quadratic_product_formula ground_quadratic_formula ground_product product_add_left
  product_add_right quadratic_self_products charged_self_products quadratic_charged_products
  charged_quadratic_products translation_quadratic
  from D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector

namespace D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateReconstruction LatticeSugawaraConformal
open scoped BigOperators VertexOperator

noncomputable section

private theorem mixed_expansion (L : LatticeData) (a b : Charge L) (s t : ℂ) (k : ℤ) :
    mu L (vector L a s) k (vector L b t) =
      (1 / 256 : ℂ) • mu L (quadraticState L a) k (quadraticState L b) +
      (t / 64) • mu L (quadraticState L a) k (chargedState L b) +
      (s / 64) • mu L (chargedState L a) k (quadraticState L b) +
      (s * t / 16) • mu L (chargedState L a) k (chargedState L b) := by
  simp only [vector, mu, map_add, map_smul, VertexOperator.ncoeff, Pi.add_apply,
    Pi.smul_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_add, smul_smul]
  module

/-- The opposite signs in one norm-four direction have no singular mutual products. -/
theorem opposite_sign_products (L : LatticeData) (a : Charge L) (ha : bilinear L a a = 4)
    (s : ℂ) (hs : s ^ 2 = 1) (k : ℤ) (hk : 0 ≤ k) :
    mu L (vector L a s) k (vector L a (-s)) = 0 := by
  obtain ⟨q0, q1, q2, q3, qt⟩ := quadratic_self_products L a ha
  obtain ⟨b0, b1, b2, b3, bt⟩ := charged_self_products L a ha
  obtain ⟨qb0, qb1, qbt⟩ := quadratic_charged_products L a ha
  obtain ⟨bq0, bq1, bqt⟩ := charged_quadratic_products L a ha
  have b0' : mu L (chargedState L a) 0 (chargedState L a) =
      (1 / 2 : ℂ) • LatticeSugawaraConformal.translation L (quadraticState L a) := by
    rw [b0, translation_quadratic]
    norm_num [smul_smul]
  have hss : s * -s / 16 = -(1 / 16 : ℂ) := by
    rw [mul_neg, ← pow_two, hs]
    ring
  rw [mixed_expansion, hss]
  obtain h | h | h | h | h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k := by omega
  · rw [h, q0, qb0, bq0, b0']
    module
  · rw [h, q1, qb1, bq1, b1]
    module
  · rw [h, q2, qbt 2 (by omega), bqt 2 (by omega), b2]
    simp
  · rw [h, q3, qbt 3 (by omega), bqt 3 (by omega), b3]
    module
  · rw [qt k h, qbt k (by omega), bqt k (by omega), bt k h]
    simp

private theorem current_on_orthogonal_quadratic (L : LatticeData) (a b : Charge L) (hab : bilinear L a b = 0)
    (k : ℤ) (hk : 0 ≤ k) : currentMode L a k (quadraticState L b) = 0 := by
  rw [quadraticState, currentMode_single]
  by_cases hz : k = 0
  · subst k
    simp [neutralPolynomialMode, bilinear]
  · simp only [neutralPolynomialMode, not_lt.mpr hk, hz, ite_false, LinearMap.smul_apply,
      LinearMap.sum_apply, Derivation.coeFn_coe, partial_quadratic]
    by_cases hr : (k - 1).toNat = 0
    · have hone : k = 1 := by omega
      subst k
      have hs : (∑ i : Fin L.rank, ∑ j : Fin L.rank,
          (a i : ℂ) * (L.G i j : ℂ) * (b j : ℂ)) = 0 := by
        exact_mod_cast hab
      simp only [Int.reduceSub, Int.toNat_zero, ite_true, Int.cast_one, one_smul]
      simp only [Finset.smul_sum, smul_smul]
      have hh (i j : Fin L.rank) :
          (a i : ℂ) * ((L.G i j : ℂ) * (2 * (b j : ℂ))) =
             2 * ((a i : ℂ) * (L.G i j : ℂ) * (b j : ℂ)) := by ring
      have hscale : (∑ i : Fin L.rank, ∑ j : Fin L.rank,
          ((a i : ℂ) * ((L.G i j : ℂ) * (2 * (b j : ℂ)))) • chargePolynomial L b) = 0 := by
        simp only [hh, ← Finset.sum_smul, ← Finset.mul_sum, hs, mul_zero, zero_smul]
      rw [hscale, Finsupp.single_zero]
    · simp only [hr, ite_false, smul_zero, Finset.sum_const_zero, Finsupp.single_zero]

/-- Orthogonal directions have no singular mutual products for any scalar signs. -/
theorem orthogonal_products (L : LatticeData) (a b : Charge L) (hab : bilinear L a b = 0)
    (s t : ℂ) (k : ℤ) (hk : 0 ≤ k) : mu L (vector L a s) k (vector L b t) = 0 := by
  have quadratic_vanish (v : Carrier L)
      (h : ∀ r : ℤ, 0 ≤ r → currentMode L a r v = 0) :
      mu L (quadraticState L a) k v = 0 := by
    rw [quadratic_product_formula]
    have hj (j : ℕ) : currentMode L a (k + j) v = 0 := h _ (by omega)
    have hj' (j : ℕ) : currentMode L a j v = 0 := h _ (by omega)
    simp only [hj, hj', map_zero, finsum_zero, add_zero]
  have q_b (c : Charge L) (h : bilinear L a c = 0) :
      mu L (quadraticState L a) k (ground L c) = 0 := by
    apply quadratic_vanish
    intro r hr
    simp [currentMode_ground L a c r hr, h]
  have b_q (c : Charge L) (h : bilinear L c b = 0) :
      mu L (ground L c) k (quadraticState L b) = 0 := by
    simp [ground_quadratic_formula, h, creationCoeff, show -k - 1 < 0 by omega]
  have b_b (c d : Charge L) (h : bilinear L c d = 0) :
      mu L (ground L c) k (ground L d) = 0 := by
    simp [ground_product, h, creationCoeff, show -k - 1 < 0 by omega]
  have h_neg_r : bilinear L a (-b) = 0 := by simp [bilinear_neg_right, hab]
  have h_neg_l : bilinear L (-a) b = 0 := by simp [bilinear_neg_left, hab]
  have h_neg_both : bilinear L (-a) (-b) = 0 := by
    simp [bilinear_neg_left, h_neg_r]
  rw [mixed_expansion, quadratic_vanish _ (current_on_orthogonal_quadratic L a b hab)]
  simp only [chargedState, product_add_left, product_add_right, q_b _ hab, q_b _ h_neg_r,
    b_q _ hab, b_q _ h_neg_l, b_b _ _ hab, b_b _ _ h_neg_r, b_b _ _ h_neg_l,
    b_b _ _ h_neg_both, add_zero, smul_zero]

end
end D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector
