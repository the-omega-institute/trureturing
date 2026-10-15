/- GID: D5/S3/VertexAlgebra/BcGhostVacuum
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostVacuum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full infinite ghost stress operator has cubic positive-mode vacuum contraction. -/

import D5.S3.VertexAlgebra.BcGhostStressCurrent
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Bernoulli

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostVacuum
noncomputable section

open D5.S3.VertexAlgebra.BcGhostFockSupport
open D5.S3.VertexAlgebra.BcGhostExteriorOperators
open D5.S3.VertexAlgebra.BcGhostStressCurrent

variable {K : Type*} [CommRing K]

private theorem annihilate_vacuum (i : ℕ) :
    annihilate (K := K) i vacuum = 0 := by
  simp [vacuum, annihilate, Finsupp.linearCombination_single, annihilateBasis]

private theorem b_vacuum (m : ℤ) (hm : -1 ≤ m) : b (K := K) m vacuum = 0 := by
  have h : ¬ m ≤ -2 := by omega
  simp [b, h, annihilate_vacuum]

private theorem c_vacuum (n : ℤ) (hn : 2 ≤ n) : c (K := K) n vacuum = 0 := by
  have h : ¬ n ≤ 1 := by omega
  simp [c, h, annihilate_vacuum]

private theorem normal_pair_vacuum (p q : ℤ) :
    normalPair (K := K) p q vacuum =
      if p ≤ -2 ∧ q ≤ 1 then b p (c q vacuum) else 0 := by
  by_cases hp : p ≤ -2
  · by_cases hq : q ≤ 1
    · simp [normalPair, hp, hq]
    · simp [normalPair, hp, hq, c_vacuum q (by omega)]
  · simp [normalPair, hp, b_vacuum p (by omega)]

/-- Every stress mode at or above minus one annihilates the actual algebraic vacuum. -/
theorem L_vacuum_annihilation (m : ℤ) (hm : -1 ≤ m) :
    L (K := K) m vacuum = 0 := by
  rw [L_interval_sum m vacuum (-cutoff m vacuum) (cutoff m vacuum) le_rfl le_rfl]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases h : m + k ≤ -2 ∧ -k ≤ 1
  · have hmk : m = k := by omega
    simp [hmk]
  · simp [normal_pair_vacuum, h]

private theorem annihilate_create_vacuum (i : ℕ) :
    annihilate (K := K) i (create i vacuum) = vacuum := by
  apply exteriorCoordinates.injective
  rw [exterior_annihilate, exterior_create]
  unfold exteriorContraction
  rw [CliffordAlgebra.contractLeft_ι_mul]
  have hz : exteriorContraction (K := K) i (exteriorCoordinates vacuum) = 0 := by
    rw [← exterior_annihilate, annihilate_vacuum, map_zero]
  change _ • exteriorCoordinates vacuum -
    _ * exteriorContraction i (exteriorCoordinates vacuum) = _
  rw [hz]
  simp

private theorem b_c_vacuum (k : ℤ) (hk : -1 ≤ k) :
    b (K := K) k (c (-k) vacuum) = vacuum := by
  have hb : ¬ k ≤ -2 := by omega
  have hc : -k ≤ 1 := by omega
  have hind : 2 * (1 - -k).toNat + 1 = 2 * (k + 1).toNat + 1 := by omega
  simpa only [b, c, if_neg hb, if_pos hc, hind] using
    annihilate_create_vacuum (K := K) (2 * (k + 1).toNat + 1)

private theorem L_negative_vacuum (r : ℤ) :
    L (K := K) (-r) vacuum =
      ∑ k ∈ Finset.Icc (-1) (r - 2),
        (-r - k : K) • b (-r + k) (c (-k) vacuum) := by
  let a : ℤ := min (-cutoff (-r) (vacuum : Fock K)) (-1)
  let z : ℤ := max (cutoff (-r) (vacuum : Fock K)) (r - 2)
  have ha : a ≤ -cutoff (-r) (vacuum : Fock K) := min_le_left _ _
  have hz : cutoff (-r) (vacuum : Fock K) ≤ z := le_max_left _ _
  have hsub : Finset.Icc (-1) (r - 2) ⊆ Finset.Icc a z := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr
      ⟨(min_le_right _ _).trans hk'.1, hk'.2.trans (le_max_right _ _)⟩
  rw [L_interval_sum (-r) vacuum a z ha hz,
    ← Finset.sum_subset hsub (fun k hk hnot => ?_)]
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have h : -r + k ≤ -2 ∧ -k ≤ 1 := by omega
    simp only [normal_pair_vacuum, if_pos h, Int.cast_neg]
  · have h : ¬ (-r + k ≤ -2 ∧ -k ≤ 1) := by
      intro hp
      apply hnot
      exact Finset.mem_Icc.mpr (by omega)
    simp only [normal_pair_vacuum, if_neg h, smul_zero]

private theorem L_positive_pair (r k : ℤ) (hr : 0 < r)
    (hk : k ∈ Finset.Icc (-1) (r - 2)) :
    L (K := K) r (b (-r + k) (c (-k) vacuum)) = (2 * r - k : K) • vacuum := by
  have hk' := Finset.mem_Icc.mp hk
  have hrv : L (K := K) r vacuum = 0 := L_vacuum_annihilation r (by omega)
  have hcv : c (K := K) (r + -k) vacuum = 0 := c_vacuum _ (by omega)
  have hc := congrArg (fun X : Module.End K (Fock K) => X vacuum)
    (L_c_commutator (K := K) r (-k))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    hrv, map_zero, sub_zero, hcv, smul_zero] at hc
  have hb := congrArg (fun X : Module.End K (Fock K) => X (c (-k) vacuum))
    (L_b_commutator (K := K) r (-r + k))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    hc, map_zero, sub_zero] at hb
  have hidx : r + (-r + k) = k := by omega
  rw [hidx, b_c_vacuum k hk'.1] at hb
  have hcoef : (r : K) - ((-r + k : ℤ) : K) = 2 * (r : K) - (k : K) := by
    push_cast
    ring
  rw [hcoef] at hb
  exact hb

/-- Positive modes contract the actual negative-mode vacuum vector to a vacuum multiple.
The interval is the surviving double-creator interval, not a truncation of the carrier. -/
private theorem L_vacuum_contraction_sum (r : ℤ) (hr : 0 < r) :
    L (K := K) r (L (-r) vacuum) =
      ∑ k ∈ Finset.Icc (-1) (r - 2), ((-r - k) * (2 * r - k) : K) • vacuum := by
  rw [L_negative_vacuum, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul, L_positive_pair r k hr hk, smul_smul]

private theorem coefficient_sum_six (r : ℤ) (hr : 0 < r) :
    6 * (∑ k ∈ Finset.Icc (-1) (r - 2), (-r - k) * (2 * r - k)) =
      -13 * (r ^ 3 - r) := by
  have hQ : (6 : ℚ) * (∑ k ∈ Finset.Icc (-1) (r - 2),
      (-(r : ℚ) - (k : ℚ)) * (2 * (r : ℚ) - (k : ℚ))) =
      -13 * ((r : ℚ) ^ 3 - (r : ℚ)) := by
    have hn : (r - 2 + 1 - (-1)).toNat = r.toNat := by omega
    have hcast : (r : ℚ) = (r.toNat : ℚ) := by
      exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hr)).symm
    rw [Int.Icc_eq_finset_map, Finset.sum_map]
    simp only [hn, Function.Embedding.trans_apply]
    change (6 : ℚ) * (∑ i ∈ Finset.range r.toNat,
      (-(r : ℚ) - ((-1 + (i : ℤ) : ℤ) : ℚ)) *
        (2 * (r : ℚ) - ((-1 + (i : ℤ) : ℤ) : ℚ))) = _
    simp_rw [Int.cast_add, Int.cast_neg, Int.cast_one, Int.cast_natCast, hcast]
    have h1 := sum_range_pow r.toNat 1
    have h2 := sum_range_pow r.toNat 2
    norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli_one, bernoulli_two] at h1 h2
    calc
      _ = 6 * (∑ i ∈ Finset.range r.toNat, ((i : ℚ) ^ 2 -
          ((r.toNat : ℚ) + 2) * (i : ℚ) +
          (-2 * (r.toNat : ℚ) ^ 2 + (r.toNat : ℚ) + 1))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = -13 * ((r.toNat : ℚ) ^ 3 - (r.toNat : ℚ)) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [h1, h2]
        ring
  exact_mod_cast hQ

private theorem coefficient_sum_quotient (r : ℤ) (hr : 0 < r) :
    (∑ k ∈ Finset.Icc (-1) (r - 2), (-r - k) * (2 * r - k)) =
      -13 * (r ^ 3 - r) / 6 := by
  rw [← coefficient_sum_six r hr, Int.mul_ediv_cancel_left _ (by decide : (6 : ℤ) ≠ 0)]

/-- The cubic scalar is an exact integer quotient, transported to any commutative ring.
No invertibility of six and no nontriviality hypothesis on the coefficient ring is needed. -/
theorem L_vacuum_contraction (r : ℤ) (hr : 0 < r) :
    L (K := K) r (L (-r) vacuum) =
      (((-13 * (r ^ 3 - r) / 6 : ℤ) : K)) • vacuum := by
  rw [L_vacuum_contraction_sum r hr, ← Finset.sum_smul]
  have hs : (∑ k ∈ Finset.Icc (-1) (r - 2), ((-r - k) * (2 * r - k) : K)) =
      ((-13 * (r ^ 3 - r) / 6 : ℤ) : K) := by
    have h := congrArg (fun z : ℤ => (z : K)) (coefficient_sum_quotient r hr)
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_sub, Int.cast_neg, Int.cast_ofNat] using h
  rw [hs]

#print axioms L_vacuum_annihilation
#print axioms L_vacuum_contraction

end
end D5.S3.VertexAlgebra.BcGhostVacuum
