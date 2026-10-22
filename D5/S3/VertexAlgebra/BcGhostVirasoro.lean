/- GID: D5/S3/VertexAlgebra/BcGhostVirasoro
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostVirasoro
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual signed ghost stress modes satisfy integral Virasoro at central charge -26. -/

/-
proof_shape: L_virasoro: content
escape_witness: Off-diagonal products of actual stress modes have zero vacuum
  coordinate: a creation operator cannot reach the empty subset, and a deletion
  of a one-creator vacuum vector reaches it only at the matching integer mode.
  This identifies the scalar commutant without any characteristic assumption.
admission_basis: escape-witness
-/

import D5.S3.VertexAlgebra.BcGhostFockCommutant
import D5.S3.VertexAlgebra.BcGhostVacuum
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Int.ModEq

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostVirasoro

noncomputable section

open BcGhostFockSupport BcGhostStressCurrent BcGhostFockCommutant BcGhostVacuum

variable {K : Type*} [CommRing K]

attribute [local instance] LieRing.ofAssociativeRing

private theorem defect_commutes (X : ℤ → Module.End K (Fock K)) (weight : ℤ)
    (hX : ∀ a t : ℤ, ⁅L (K := K) a, X t⁆ = (weight * a - t : K) • X (a + t))
    (m n t : ℤ) :
    (L (K := K) m * L n - L n * L m - (m - n : K) • L (m + n) :
      Module.End K (Fock K)).comp (X t) =
      (X t).comp (L m * L n - L n * L m - (m - n : K) • L (m + n)) := by
  change (L (K := K) m * L n - L n * L m - (m - n : K) • L (m + n)) * X t =
    X t * (L (K := K) m * L n - L n * L m - (m - n : K) • L (m + n))
  apply sub_eq_zero.mp
  change ⁅⁅L (K := K) m, L (K := K) n⁆ -
    (m - n : K) • L (K := K) (m + n), X t⁆ = 0
  simp only [sub_lie, smul_lie, lie_lie, lie_smul, hX]
  rw [show m + (n + t) = m + n + t by omega,
    show n + (m + t) = m + n + t by omega]
  simp only [smul_smul, ← sub_smul]
  have hcoef : (weight * n - t : K) * (weight * m - (n + t) : K) -
      (weight * m - t : K) * (weight * n - (m + t) : K) -
      (m - n : K) * (weight * (m + n) - t : K) = 0 := by
    ring
  simp only [Int.cast_add]
  rw [hcoef, zero_smul]

private theorem create_empty (i : ℕ) (v : Fock K) : (create i v) ∅ = 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [map_add, hv, hw]
  | single S a =>
      by_cases hi : i ∈ S <;>
        simp [create, Finsupp.linearCombination_single, createBasis, hi]

private theorem b_creator_empty (p : ℤ) (hp : p ≤ -2) (v : Fock K) :
    (b p v) ∅ = 0 := by
  simpa only [b, if_pos hp] using create_empty (K := K) _ v

private theorem b_vacuum_zero (p : ℤ) (hp : ¬ p ≤ -2) : b (K := K) p vacuum = 0 := by
  simp [b, hp, vacuum, annihilate, Finsupp.linearCombination_single, annihilateBasis]

private theorem c_vacuum_zero (q : ℤ) (hq : ¬ q ≤ 1) : c (K := K) q vacuum = 0 := by
  simp [c, hq, vacuum, annihilate, Finsupp.linearCombination_single, annihilateBasis]

private theorem b_c_empty (p q : ℤ) (hq : q ≤ 1) (hpq : p + q ≠ 0) :
    (b (K := K) p (c q vacuum)) ∅ = 0 := by
  classical
  by_cases hp : p ≤ -2
  · exact b_creator_empty p hp _
  · have hidx : (p + 1).toNat ≠ (1 - q).toNat := by omega
    simp [b, hp, c, hq, vacuum, create, createBasis, sign,
      annihilate, annihilateBasis, Finsupp.linearCombination_single, hidx]

private theorem L_pair_empty (m p q : ℤ) (hp : p ≤ -2) (hq : q ≤ 1)
    (hmpq : m + p + q ≠ 0) :
    (L (K := K) m (b p (c q vacuum))) ∅ = 0 := by
  have hcov := congrArg (fun T : Module.End K (Fock K) => (T (c q vacuum)) ∅)
    (L_b_commutator (K := K) m p)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Finsupp.sub_apply,
    LinearMap.smul_apply, Finsupp.smul_apply] at hcov
  rw [b_creator_empty p hp, sub_zero, b_c_empty (m + p) q hq hmpq, smul_zero] at hcov
  exact hcov

private theorem normal_pair_empty (p q : ℤ) :
    (normalPair (K := K) p q vacuum) ∅ = 0 := by
  by_cases hp : p ≤ -2
  · simpa only [normalPair, if_pos hp, LinearMap.comp_apply] using b_creator_empty p hp _
  · simp [normalPair, hp, b_vacuum_zero p hp]

private theorem L_vacuum_empty (m : ℤ) : (L (K := K) m vacuum) ∅ = 0 := by
  classical
  rw [L_interval_sum m vacuum (-cutoff m vacuum) (cutoff m vacuum) le_rfl le_rfl]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, normal_pair_empty, smul_zero,
    Finset.sum_const_zero]

private theorem L_product_empty (m n : ℤ) (hmn : m + n ≠ 0) :
    (L (K := K) m (L n vacuum)) ∅ = 0 := by
  classical
  rw [L_interval_sum n vacuum (-cutoff n vacuum) (cutoff n vacuum) le_rfl le_rfl]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hp : n + k ≤ -2
  · by_cases hq : -k ≤ 1
    · have hzero := L_pair_empty (K := K) m (n + k) (-k) hp hq (by omega)
      simp only [normalPair, if_pos hp, LinearMap.comp_apply, hzero, smul_zero]
    · simp [normalPair, hp, c_vacuum_zero (-k) hq]
  · simp [normalPair, hp, b_vacuum_zero (n + k) hp]

private theorem cubic_dvd_six (m : ℤ) : (6 : ℤ) ∣ -13 * (m ^ 3 - m) := by
  apply Int.dvd_iff_emod_eq_zero.mpr
  have hbound : 0 ≤ m % 6 ∧ m % 6 < 6 :=
    ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
  have hres : m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨
      m % 6 = 4 ∨ m % 6 = 5 := by omega
  have hpow : m ^ 3 % 6 = (m % 6) ^ 3 % 6 :=
    Int.ModEq.pow 3 (by simp [Int.ModEq])
  rw [Int.mul_emod, Int.sub_emod, hpow]
  rcases hres with hres | hres | hres | hres | hres | hres <;> rw [hres] <;> norm_num

private theorem cubic_quotient_neg (m : ℤ) :
    -13 * ((-m) ^ 3 - -m) / 6 = -(-13 * (m ^ 3 - m) / 6) := by
  rw [show -13 * ((-m) ^ 3 - -m) = -(-13 * (m ^ 3 - m)) by ring]
  exact Int.neg_ediv_of_dvd (cubic_dvd_six m)

private theorem commutator_vacuum_empty (m n : ℤ) :
    ((L (K := K) m * L n - L n * L m : Module.End K (Fock K)) vacuum) ∅ =
      if m + n = 0 then ((-13 * (m ^ 3 - m) / 6 : ℤ) : K) else 0 := by
  by_cases hmn : m + n = 0
  · have hn : n = -m := by omega
    subst n
    simp only [add_neg_cancel, if_true]
    rcases lt_trichotomy 0 m with hm | hm | hm
    · have hvac := L_vacuum_annihilation (K := K) m (by omega)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hvac, map_zero, sub_zero]
      rw [L_vacuum_contraction m hm]
      simp [vacuum]
    · subst m
      simp
    · have hvac := L_vacuum_annihilation (K := K) (-m) (by omega)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hvac, map_zero, zero_sub]
      have hcontract := L_vacuum_contraction (K := K) (-m) (by omega)
      simp only [neg_neg] at hcontract
      rw [hcontract]
      simp only [Finsupp.neg_apply, Finsupp.smul_apply, vacuum,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
      rw [cubic_quotient_neg, Int.cast_neg, neg_neg]
  · rw [if_neg hmn]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Finsupp.sub_apply,
      L_product_empty m n hmn, L_product_empty n m (by omega), sub_self]

/-- Every pair of actual ghost stress modes satisfies the full unscaled integral
Virasoro relation on the infinite algebraic Fock carrier over every commutative ring. -/
theorem L_virasoro (m n : ℤ) :
    L (K := K) m * L n - L n * L m =
      (m - n : K) • L (m + n) +
        (if m + n = 0 then ((-13 * (m ^ 3 - m) / 6 : ℤ) : K) else 0) • LinearMap.id := by
  have hb := defect_commutes (K := K) (b (K := K)) 1 (by
    intro a t
    simpa [Ring.lie_def] using L_b_commutator (K := K) a t) m n
  have hc := defect_commutes (K := K) (c (K := K)) (-2) (by
    intro a t
    simpa [Ring.lie_def] using L_c_commutator (K := K) a t) m n
  have hscalar := mode_commutant_scalar (K := K)
    (L m * L n - L n * L m - (m - n : K) • L (m + n)) hb hc
  have hcoord :
      ((L (K := K) m * L n - L n * L m - (m - n : K) • L (m + n) :
        Module.End K (Fock K)) vacuum) ∅ =
        if m + n = 0 then ((-13 * (m ^ 3 - m) / 6 : ℤ) : K) else 0 := by
    simp only [LinearMap.sub_apply, Finsupp.sub_apply, LinearMap.smul_apply,
      Finsupp.smul_apply, L_vacuum_empty, smul_zero, sub_zero]
    exact commutator_vacuum_empty m n
  rw [hcoord] at hscalar
  exact sub_eq_iff_eq_add'.mp hscalar

#print axioms L_virasoro

end
end D5.S3.VertexAlgebra.BcGhostVirasoro
