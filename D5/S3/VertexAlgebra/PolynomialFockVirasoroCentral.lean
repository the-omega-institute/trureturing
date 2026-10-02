/- GID: D5/S3/VertexAlgebra/PolynomialFockVirasoroCentral
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/PolynomialFockVirasoroCentral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual polynomial Fock Sugawara operators satisfy the all-integer central relation. -/

/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors: Kalle Kytölä
Modified source: original proof transplanted from VirasoroProject revision
5ff4245383b2cdd4eea7a0524bc1274c32041eb4, Sugawara.lean through line 571
and CentralChargeCalc.lean lines 35-76. Specialized to the existing complex
polynomial Fock operators; frozen support and current commutators replace
upstream premises, and normalization helpers are inlined as local proof steps.
proof_shape: L_commutator: content
escape_witness: The live normal-ordering boundary sum is evaluated on the two
integer sign intervals and yields the cubic central coefficient.
admission_basis: escape-witness
-/

import D5.S3.VertexAlgebra.PolynomialFockSugawaraCommutators

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.PolynomialFockVirasoroCentral

open D5.S3.VertexAlgebra.PolynomialFockSugawaraSupport
open D5.S3.VertexAlgebra.PolynomialFockSugawaraCommutators

set_option maxHeartbeats 4000000 in
-- The transplanted interval calculations are inlined to retain only the central theorem.
/-- The actual rank-one polynomial Fock operators satisfy the Virasoro relation at c = 1.
The original central boundary calculation is inlined without companion declarations. -/
theorem L_commutator (n m : ℤ) :
    L n * L m - L m * L n = ((n : ℂ) - (m : ℂ)) • L (n + m)
      + (if n + m = 0 then (((n : ℂ) ^ 3 - (n : ℂ)) / 12) •
          (1 : Module.End ℂ Fock) else 0) := by
  classical
  let comm : Module.End ℂ Fock → Module.End ℂ Fock → Module.End ℂ Fock :=
    fun left right => left * right - right * left
  have support (s : ℤ) (p : Fock) : Function.HasFiniteSupport
      (fun k : ℤ => normalPair (s - k) k p) :=
    (Set.finite_Ioo _ _).subset (normalPair_support_interval s p)
  have shiftedSupport (s t : ℤ) (p : Fock) : Function.HasFiniteSupport
      (fun k : ℤ => normalPair (s - k) (t + k) p) := by
    have shifted := (support (s + t) p).fun_comp_of_injective
      (g := fun k : ℤ => t + k) (fun _ _ equality => add_left_cancel equality)
    simpa only [show ∀ k : ℤ, s + t - (t + k) = s - k by
      intro k; ring] using shifted
  have pairBoundary (k l : ℤ) : normalPair k l = mode k * mode l
      - (if 0 ≤ k ∧ k + l = 0 then (k : ℂ) else 0) • 1 := by
    have commute (hk : k + l ≠ 0) : mode k * mode l = mode l * mode k := by
      exact sub_eq_zero.mp (by simpa [hk] using mode_heisenberg k l)
    by_cases hk : 0 ≤ k
    · by_cases hlk : l ≤ k
      · simp only [normalPair, hlk, if_true, true_and, hk,
          ← Module.End.mul_eq_comp]
        have hh := mode_heisenberg k l
        by_cases hkl : k + l = 0
        · simp only [hkl, if_true] at hh ⊢
          exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using
            (sub_eq_iff_eq_add.mp hh).symm)
        · simp only [hkl, if_false, zero_smul, sub_zero]
          exact (commute hkl).symm
      · have hkl : k + l ≠ 0 := by omega
        simp [normalPair, hlk, hk, hkl, Module.End.mul_eq_comp]
    · by_cases hlk : l ≤ k
      · have hkl : k + l ≠ 0 := by omega
        simpa only [normalPair, hlk, if_true, hk, false_and, if_false,
          zero_smul, sub_zero, ← Module.End.mul_eq_comp] using (commute hkl).symm
      · simp [normalPair, hlk, hk, Module.End.mul_eq_comp]
  have product (s k l : ℤ) : comm (L s) (mode k * mode l) =
      -(l : ℂ) • (mode k * mode (s + l))
        + -(k : ℂ) • (mode (s + k) * mode l) := by
    have expand : comm (L s) (mode k * mode l) =
        mode k * comm (L s) (mode l) + comm (L s) (mode k) * mode l := by
      dsimp [comm]
      noncomm_ring
    rw [expand]
    change _ * (L s * mode l - mode l * L s) +
      (L s * mode k - mode k * L s) * _ = _
    rw [L_mode_commutator, L_mode_commutator]
    simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  have pairCommutator (s t k : ℤ) : comm (L s) (normalPair (t - k) k) =
      -(k : ℂ) • normalPair (t - k) (s + k)
        + -((t : ℂ) - k) • normalPair (s + t - k) k
        + (if s + t = 0 then
             (k : ℂ) * ((s : ℂ) + k)
               * ((if k + s ≤ 0 then (1 : ℂ) else 0) - (if k ≤ 0 then (1 : ℂ) else 0))
           else 0) • 1 := by
    have first : comm (L s) (normalPair (t - k) k) =
        comm (L s) (mode (t - k) * mode k) := by
      rw [pairBoundary]
      simp [comm, mul_sub, sub_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    rw [first, product, show s + (t - k) = s + t - k by ring,
      pairBoundary (t - k) (s + k), pairBoundary (s + t - k) k]
    by_cases hst : s + t = 0
    · obtain rfl : t = -s := by omega
      match_scalars
      · ring
      · ring
      · split_ifs <;> first | (exfalso; omega) | ring
    · have h₁ : ¬ (0 ≤ t - k ∧ (t - k) + (s + k) = 0) := by omega
      have h₂ : ¬ (0 ≤ s + t - k ∧ (s + t - k) + k = 0) := by omega
      simp only [hst, h₁, h₂, if_false, zero_smul, sub_zero, add_zero]
      match_scalars <;> ring
  have sum_Ico_id (a b : ℤ) (hab : a ≤ b) :
      ∑ x ∈ Finset.Ico a b, (x : ℂ) = ((a : ℂ) + b - 1) * ((b : ℂ) - a) / 2 := by
    induction b, hab using Int.leInduction with
    | base => simp
    | succ b hb ih =>
      have hins : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hins, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega), ih]
      push_cast; ring
  have sum_Ico_sq (a b : ℤ) (hab : a ≤ b) :
      ∑ x ∈ Finset.Ico a b, (x : ℂ) ^ 2
        = ((b : ℂ) - 1) * (b : ℂ) * (2 * (b : ℂ) - 1) / 6
          - ((a : ℂ) - 1) * (a : ℂ) * (2 * (a : ℂ) - 1) / 6 := by
    induction b, hab using Int.leInduction with
    | base => simp
    | succ b hb ih =>
      have hins : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hins, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega), ih]
      push_cast; ring
  have sum_Ico_quadratic (a b : ℤ) (hab : a ≤ b) (c₂ c₁ c₀ : ℂ) :
      ∑ x ∈ Finset.Ico a b, (c₂ * (x : ℂ) ^ 2 + c₁ * (x : ℂ) + c₀)
        = c₂ * (((b : ℂ) - 1) * (b : ℂ) * (2 * (b : ℂ) - 1) / 6
                - ((a : ℂ) - 1) * (a : ℂ) * (2 * (a : ℂ) - 1) / 6)
          + c₁ * (((a : ℂ) + b - 1) * ((b : ℂ) - a) / 2)
          + c₀ * ((b : ℂ) - a) := by
    have hcard : ((Finset.Ico a b).card : ℂ) = (b : ℂ) - a := by
      rw [Int.card_Ico]
      exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ b - a)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul, hcard, sum_Ico_id a b hab, sum_Ico_sq a b hab]
    ring
  have normalSum (n m : ℤ) (v : Fock) :
      ∑ᶠ k : ℤ, (-(k : ℂ) • normalPair (m - k) (n + k) v
          + -((m : ℂ) - k) • normalPair (n + m - k) k v)
        = ((n : ℂ) - m) • ∑ᶠ k : ℤ, normalPair (n + m - k) k v := by
    have var_change : ∑ᶠ k : ℤ, -(k : ℂ) • normalPair (m - k) (n + k) v
        = ∑ᶠ k : ℤ, ((n : ℂ) - k) • normalPair (n + m - k) k v := by
      rw [← finsum_comp_equiv (Equiv.subRight n)]
      refine finsum_congr fun k ↦ ?_
      simp only [Equiv.subRight_apply]
      rw [show m - (k - n) = n + m - k by ring, show n + (k - n) = k by ring]
      congr 1
      push_cast
      ring
    calc  ∑ᶠ k : ℤ, (-(k : ℂ) • normalPair (m - k) (n + k) v
              + -((m : ℂ) - k) • normalPair (n + m - k) k v)
      _ = ∑ᶠ k : ℤ, -(k : ℂ) • normalPair (m - k) (n + k) v
            + ∑ᶠ k : ℤ, -((m : ℂ) - k) • normalPair (n + m - k) k v :=
          finsum_add_distrib ?_ ?_
      _ = ∑ᶠ k : ℤ, ((n : ℂ) - k) • normalPair (n + m - k) k v
            + ∑ᶠ k : ℤ, -((m : ℂ) - k) • normalPair (n + m - k) k v := by rw [var_change]
      _ = ∑ᶠ k : ℤ, (((n : ℂ) - k) • normalPair (n + m - k) k v
            + -((m : ℂ) - k) • normalPair (n + m - k) k v) := (finsum_add_distrib ?_ ?_).symm
      _ = ∑ᶠ k : ℤ, ((n : ℂ) - m) • normalPair (n + m - k) k v := by
          refine finsum_congr fun k ↦ ?_
          rw [← add_smul]
          congr 1
          ring
      _ = ((n : ℂ) - m) • ∑ᶠ k : ℤ, normalPair (n + m - k) k v :=
          (smul_finsum' _ (support (n + m) v)).symm
    · exact Function.HasFiniteSupport.smul_right (fun k : ℤ => -(k : ℂ))
        (shiftedSupport m n v)
    · exact Function.HasFiniteSupport.smul_right (fun k : ℤ => -((m : ℂ) - k))
        (support (n + m) v)
    · exact Function.HasFiniteSupport.smul_right (fun k : ℤ => (n : ℂ) - k)
        (support (n + m) v)
    · exact Function.HasFiniteSupport.smul_right (fun k : ℤ => -((m : ℂ) - k))
        (support (n + m) v)
  let ccTermInt (s k : ℤ) : ℂ :=
    (k : ℂ) * ((s : ℂ) + k)
      * ((if k + s ≤ 0 then (1 : ℂ) else 0) - (if k ≤ 0 then (1 : ℂ) else 0))
  have ccTermInt_eq_zero_of_not_mem (n k : ℤ)
      (hk : k < min 0 (-n) ∨ max 0 (-n) < k) :
      ccTermInt n k = 0 := by
    rcases hk with hk | hk
    · simp [ccTermInt, show k + n ≤ 0 by omega, show k ≤ 0 by omega]
    · simp [ccTermInt, show ¬ k + n ≤ 0 by omega, show ¬ k ≤ 0 by omega]
  have hasFiniteSupport_ccTermInt (n : ℤ) :
      Function.HasFiniteSupport fun k : ℤ ↦ ccTermInt n k := by
    apply (Set.finite_Icc (min 0 (-n)) (max 0 (-n))).subset
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    simp only [Set.mem_Icc]
    by_contra hk'
    exact hk (ccTermInt_eq_zero_of_not_mem n k (by omega))
  have sugawaraGen_cc_sum (n : ℤ) :
      ∑ᶠ k : ℤ, ccTermInt n k = ((n : ℂ) ^ 3 - n) / 6 := by
    rcases le_total 0 n with hn | hn
    · rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.Ico (-n) 1) ?_]
      · rw [Finset.sum_congr rfl
              (g := fun x : ℤ ↦ (-1 : ℂ) * (x : ℂ) ^ 2 + (-(n : ℂ)) * (x : ℂ) + 0) ?_,
            sum_Ico_quadratic (-n) 1 (by omega)]
        · push_cast; ring
        · intro x hx
          simp only [Finset.mem_Ico] at hx
          by_cases hxn : x + n ≤ 0
          · obtain rfl : x = -n := by omega
            simp only [ccTermInt]
            push_cast
            ring
          · simp only [ccTermInt, if_neg hxn, if_pos (show x ≤ 0 by omega)]
            ring
      · intro k hk
        simp only [Function.mem_support, ne_eq] at hk
        simp only [Finset.coe_Ico, Set.mem_Ico]
        by_contra hk'
        exact hk (ccTermInt_eq_zero_of_not_mem n k (by omega))
    · rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.Ico 1 (1 - n)) ?_]
      · rw [Finset.sum_congr rfl
              (g := fun x : ℤ ↦ (1 : ℂ) * (x : ℂ) ^ 2 + ((n : ℂ)) * (x : ℂ) + 0) ?_,
            sum_Ico_quadratic 1 (1 - n) (by omega)]
        · push_cast; ring
        · intro x hx
          simp only [Finset.mem_Ico] at hx
          simp only [ccTermInt, if_pos (show x + n ≤ 0 by omega), if_neg (show ¬ x ≤ 0 by omega)]
          ring
      · intro k hk
        simp only [Function.mem_support, ne_eq] at hk
        simp only [Finset.coe_Ico, Set.mem_Ico]
        by_contra hk'
        apply hk
        rcases (by omega : k ≤ 0 ∨ -n < k) with h | h
        · simp [ccTermInt, h, show k + n ≤ 0 by omega]
        · simp [ccTermInt, show ¬ k ≤ 0 by omega, show ¬ k + n ≤ 0 by omega]
  apply LinearMap.ext
  intro v
  have hNO : Function.HasFiniteSupport fun k : ℤ =>
      -(k : ℂ) • normalPair (m - k) (n + k) v
        + -((m : ℂ) - k) • normalPair (n + m - k) k v :=
    (Function.HasFiniteSupport.smul_right (fun k : ℤ => -(k : ℂ))
      (shiftedSupport m n v)).add
      (Function.HasFiniteSupport.smul_right (fun k : ℤ => -((m : ℂ) - k))
        (support (n + m) v))
  have hCC : Function.HasFiniteSupport fun k : ℤ =>
      (if n + m = 0 then ccTermInt n k else 0) • v := by
    by_cases hnm : n + m = 0
    · simp only [hnm, if_true]
      exact (hasFiniteSupport_ccTermInt n).smul_left _
    · simp only [hnm, if_false, zero_smul]
      exact Function.hasFiniteSupport_fun_zero
  have expand : comm (L n) (L m) v =
      (2 : ℂ)⁻¹ • ∑ᶠ k : ℤ, comm (L n) (normalPair (m - k) k) v := by
    change L n (L m v) - L m (L n v) = _
    change L n ((2 : ℂ)⁻¹ • ∑ᶠ k : ℤ, normalPair (m - k) k v) -
      (2 : ℂ)⁻¹ • ∑ᶠ k : ℤ, normalPair (m - k) k (L n v) = _
    rw [map_smul, map_finsum _ (support m v), ← smul_sub,
      ← finsum_sub_distrib ((support m v).fun_comp (map_zero (L n))) (support m (L n v))]
    rfl
  change comm (L n) (L m) v = _
  calc comm (L n) (L m) v
      = (2 : ℂ)⁻¹ • ∑ᶠ k : ℤ, comm (L n) (normalPair (m - k) k) v := expand
    _ = (2 : ℂ)⁻¹ • ∑ᶠ k : ℤ,
        ((-(k : ℂ) • normalPair (m - k) (n + k) v
          + -((m : ℂ) - k) • normalPair (n + m - k) k v)
          + (if n + m = 0 then ccTermInt n k else 0) • v) := by
      refine congrArg _ (finsum_congr fun k => ?_)
      rw [pairCommutator]
      simp only [ccTermInt, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    _ = (2 : ℂ)⁻¹ • ((∑ᶠ k : ℤ,
        (-(k : ℂ) • normalPair (m - k) (n + k) v
          + -((m : ℂ) - k) • normalPair (n + m - k) k v))
          + ∑ᶠ k : ℤ, (if n + m = 0 then ccTermInt n k else 0) • v) := by
      rw [finsum_add_distrib hNO hCC]
    _ = ((n : ℂ) - m) • L (n + m) v
          + (2 : ℂ)⁻¹ • ∑ᶠ k : ℤ, (if n + m = 0 then ccTermInt n k else 0) • v := by
      rw [smul_add, normalSum n m v]
      congr 1
      rw [smul_comm]
      rfl
    _ = (((n : ℂ) - m) • L (n + m)
          + if n + m = 0 then (((n : ℂ) ^ 3 - n) / 12) •
              (1 : Module.End ℂ Fock) else 0) v := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, DFunLike.ite_apply,
        LinearMap.zero_apply, Module.End.one_apply]
      congr 1
      by_cases hnm : n + m = 0
      · simp only [hnm, if_true]
        rw [← finsum_smul' (hasFiniteSupport_ccTermInt n) v, sugawaraGen_cc_sum, smul_smul]
        congr 1
        ring
      · simp [hnm]

end D5.S3.VertexAlgebra.PolynomialFockVirasoroCentral
