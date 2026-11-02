/- GID: D5/S3/Arith/ModularForms/CubicThetaJacobiCube
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaJacobiCube
   mirror-E: none(waiver:formal-jacobi-lattice-cube)
   anchors: [lit/huang2025signpatterns]
   utility: none
   digest: Locally finite integer monomial sums realize the actual Jacobi series and its cube. -/

import D5.S3.Arith.ModularForms.CubicThetaJacobi
import D5.S3.Arith.ModularForms.CubicThetaShifted

/-! The complete integer sums underlying the Laurent columns of a Jacobi cube. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.CubicThetaJacobiCube

open CubicThetaJacobi CubicThetaLattice CubicThetaShifted
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

def triangularExponent (k : ℤ) : ℕ :=
  if 0 ≤ k then k.toNat.choose 2 else (k.natAbs + 1).choose 2

theorem twice_triangular (k : ℤ) :
    (2 : ℤ) * triangularExponent k = k * (k - 1) := by
  have hc (n : ℕ) : (2 : ℤ) * n.choose 2 = (n : ℤ) * ((n : ℤ) - 1) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [show (n + 1).choose 2 = n + n.choose 2 by
        simpa using Nat.choose_succ_succ n 1]
      push_cast
      nlinarith
  cases k with
  | ofNat n => simpa [triangularExponent] using hc n
  | negSucc n =>
      have h := hc (n + 2)
      simp only [triangularExponent]
      rw [if_neg (by omega)]
      have ha : (Int.negSucc n).natAbs = n + 1 := rfl
      rw [ha]
      simp only [Int.negSucc_eq]
      push_cast at h ⊢
      nlinarith

theorem triangular_bound (k : ℤ) (degree : ℕ) (h : triangularExponent k ≤ degree) :
    k ∈ Finset.Icc (-(2 * (degree : ℤ) + 2)) (2 * (degree : ℤ) + 2) := by
  have ht := twice_triangular k
  have hc : (triangularExponent k : ℤ) ≤ degree := by exact_mod_cast h
  simp only [Finset.mem_Icc]
  constructor <;> nlinarith [sq_nonneg k, sq_nonneg (k - 1)]

noncomputable def jacobiTerm (k : ℤ) : PowerSeries (LaurentPolynomial ℚ) :=
  PowerSeries.C (AddMonoidAlgebra.single k ((-1 : ℚ) ^ k.natAbs)) *
    PowerSeries.X ^ triangularExponent k

private theorem jacobiTerm_coeff_zero (degree : ℕ) (k : ℤ)
    (hk : k ∉ Finset.Icc (-(2 * (degree : ℤ) + 2)) (2 * (degree : ℤ) + 2)) :
    PowerSeries.coeff degree (jacobiTerm k) = 0 := by
  have ht : triangularExponent k ≠ degree := by
    intro h
    exact hk (triangular_bound k degree (by omega))
  rw [jacobiTerm, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
    if_neg (Ne.symm ht), mul_zero]

/-- The genuine normalized product is the locally finite sum over every integer index. -/
theorem hasSum_jacobi [TopologicalSpace (LaurentPolynomial ℚ)] :
    HasSum jacobiTerm jacobiSeries := by
  classical
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro degree
  let s := Finset.Icc (-(2 * (degree : ℤ) + 2)) (2 * (degree : ℤ) + 2)
  have hsum : HasSum (fun k => PowerSeries.coeff degree (jacobiTerm k))
      (∑ k ∈ s, PowerSeries.coeff degree (jacobiTerm k)) := hasSum_sum_of_ne_finset_zero
    (fun k hk => jacobiTerm_coeff_zero degree k hk :
      ∀ k ∉ s, PowerSeries.coeff degree (jacobiTerm k) = 0)
  suffices (∑ k ∈ s, PowerSeries.coeff degree (jacobiTerm k)) =
      PowerSeries.coeff degree jacobiSeries by simpa only [this] using hsum
  apply LaurentPolynomial.ext
  intro index
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single index]
  · have h := congrArg (PowerSeries.coeff degree) (jacobiSeries_column index)
    rw [PowerSeries.coeff_mk] at h
    change (PowerSeries.coeff degree jacobiSeries).coeff index =
      PowerSeries.coeff degree (PowerSeries.C ((-1 : ℚ) ^ index.natAbs) *
        PowerSeries.X ^ triangularExponent index) at h
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow] at h
    rw [jacobiTerm, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs with hd
    · simpa only [hd, mul_one, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_true] using h.symm
    · simpa only [hd, ite_false, mul_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using h.symm
  · intro k _ hki
    rw [jacobiTerm, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs <;> simp only [mul_one, mul_zero, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, ite_false, ne_eq, hki, Ne.symm hki,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · intro hi
    rw [jacobiTerm_coeff_zero degree index hi]
    simp

private theorem triple_summable [TopologicalSpace (LaurentPolynomial ℚ)] :
    Summable (fun p : (ℤ × ℤ) × ℤ => jacobiTerm p.1.1 * jacobiTerm p.1.2 * jacobiTerm p.2) := by
  classical
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro degree
  let s := Finset.Icc (-(2 * (degree : ℤ) + 2)) (2 * (degree : ℤ) + 2)
  apply summable_of_hasFiniteSupport
  apply ((s.product s).product s).finite_toSet.subset
  intro p hp
  have hp' : PowerSeries.coeff degree
      (jacobiTerm p.1.1 * jacobiTerm p.1.2 * jacobiTerm p.2) ≠ 0 := hp
  have ht : triangularExponent p.1.1 + triangularExponent p.1.2 +
      triangularExponent p.2 = degree := by
    contrapose! hp'
    simp only [jacobiTerm]
    rw [show PowerSeries.C (AddMonoidAlgebra.single p.1.1 ((-1 : ℚ) ^ p.1.1.natAbs)) *
          PowerSeries.X ^ triangularExponent p.1.1 *
        (PowerSeries.C (AddMonoidAlgebra.single p.1.2 ((-1 : ℚ) ^ p.1.2.natAbs)) *
          PowerSeries.X ^ triangularExponent p.1.2) *
        (PowerSeries.C (AddMonoidAlgebra.single p.2 ((-1 : ℚ) ^ p.2.natAbs)) *
          PowerSeries.X ^ triangularExponent p.2) =
        PowerSeries.C (AddMonoidAlgebra.single p.1.1 ((-1 : ℚ) ^ p.1.1.natAbs) *
          AddMonoidAlgebra.single p.1.2 ((-1 : ℚ) ^ p.1.2.natAbs) *
          AddMonoidAlgebra.single p.2 ((-1 : ℚ) ^ p.2.natAbs)) *
        PowerSeries.X ^ (triangularExponent p.1.1 + triangularExponent p.1.2 +
          triangularExponent p.2) by simp only [map_mul, pow_add]; ring]
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (Ne.symm hp'), mul_zero]
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨triangular_bound _ degree (by omega), triangular_bound _ degree (by omega)⟩,
    triangular_bound _ degree (by omega)⟩

set_option maxHeartbeats 1000000 in
-- Typeclass synthesis uses the complete product uniformity of formal power series.
/-- The cube includes all triples; local finiteness justifies the Cauchy products. -/
theorem hasSum_jacobi_cube
    [UniformSpace (LaurentPolynomial ℚ)] [DiscreteUniformity (LaurentPolynomial ℚ)] :
    HasSum (fun p : (ℤ × ℤ) × ℤ => jacobiTerm p.1.1 * jacobiTerm p.1.2 * jacobiTerm p.2)
      (jacobiSeries ^ 3) := by
  have ht := triple_summable
  have hzero : jacobiTerm 0 = 1 := by
    simp only [jacobiTerm, triangularExponent, le_refl, ite_true, Int.toNat_zero,
      Nat.choose_zero_succ, pow_zero, Int.natAbs_zero, zero_add, mul_one]
    rfl
  have hpair : Summable (fun p : ℤ × ℤ => jacobiTerm p.1 * jacobiTerm p.2) := by
    have h := ht.comp_injective (i := fun p : ℤ × ℤ => (p, (0 : ℤ)))
      (by intro p q h; exact congrArg Prod.fst h)
    simpa only [Function.comp_def, hzero, mul_one] using h
  have h := (hasSum_jacobi.mul hasSum_jacobi hpair).mul hasSum_jacobi ht
  simpa only [pow_succ, pow_zero, one_mul] using h

end D5.S3.Arith.ModularForms.CubicThetaJacobiCube
