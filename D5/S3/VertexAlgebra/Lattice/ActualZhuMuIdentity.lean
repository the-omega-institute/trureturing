/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuMuIdentity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuMuIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite binomial change of basis for the actual Zhu associator. -/

/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the repository root LICENSE.
Authors: Fedor K. Popov

Source-faithful adaptation of ZhuMu.muCoeff and ZhuMu.mu_identity from
Fedor-Popov/Lean_VOA, revision 013a799ca834a8a6b3afa8129e3e522025b3f45c,
VOA/Modules/ZhuMuIdentity.lean. The finite-difference proof uses native
Ring.choose through StateFieldResidueReconstruction.integerBinomial.
The classical source is Zhu's associativity argument, also developed in
Frenkel and Zhu's construction of the Zhu algebra.
-/

import D5.S3.VertexAlgebra.StateFieldResidueReconstruction
import Mathlib.Algebra.Group.ForwardDiff

/-! The signed-lower-index binomial transform underlying Zhu's associator. -/

set_option autoImplicit false
set_option quotPrecheck false

namespace D5.S3.VertexAlgebra.Lattice.ActualZhuMuIdentity

open Finset
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators

local notation "C(" n "," k ")" =>
  (if (0 : ℤ) ≤ (k : ℤ) then integerBinomial (n : ℤ) (k : ℤ).toNat else 0)

private theorem binomial_nat (N n : ℕ) : C((N : ℤ), (n : ℤ)) = (N.choose n : ℂ) := by
  simp [integerBinomial, Ring.choose_natCast]

private theorem binomial_above (N : ℕ) (j : ℤ) (h : (N : ℤ) < j) :
    C((N : ℤ), j) = 0 := by
  have hj : 0 ≤ j := by omega
  rw [ite_eq_left hj]
  have hNj : N < j.toNat := by omega
  simp [integerBinomial, Ring.choose_natCast, Nat.choose_eq_zero_of_lt hNj]

private theorem binomial_pascal (r j : ℤ) :
    C(r + 1, j + 1) = C(r, j) + C(r, j + 1) := by
  rcases lt_trichotomy j (-1) with hj | rfl | hj
  · simp only [ite_eq_right (by omega : ¬ 0 ≤ j + 1), ite_eq_right (by omega : ¬ 0 ≤ j),
      zero_add]
  · simp [integerBinomial]
  · have hj0 : 0 ≤ j := by omega
    have hj1 : 0 ≤ j + 1 := by omega
    simp only [ite_eq_left hj0, ite_eq_left hj1, integerBinomial]
    rw [show (j + 1).toNat = j.toNat + 1 by omega, Ring.choose_succ_succ, Int.cast_add]

private theorem binomial_difference (r j : ℤ) :
    C(r + 1, j + 1) - C(r, j) = C(r, j + 1) := by
  rw [binomial_pascal]
  ring

/-- The alternating finite difference of the diagonal binomial sequence. -/
private theorem inner_lemma (K kk : ℕ) (s : ℤ) :
    ∑ n ∈ range (kk + 1),
      (-1 : ℂ) ^ (kk - n) * C((kk : ℤ), (n : ℤ)) *
        C((K : ℤ) + (n : ℤ), s + (n : ℤ)) = C((K : ℤ), s + (kk : ℤ)) := by
  have iter (k : ℕ) : ∀ n : ℕ,
      (fwdDiff (1 : ℕ))^[k] (fun m : ℕ => C((K : ℤ) + (m : ℤ), s + (m : ℤ))) n =
        C((K : ℤ) + (n : ℤ), s + (n : ℤ) + (k : ℤ)) := by
    induction k with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      rw [Function.iterate_succ_apply']
      change (fwdDiff (1 : ℕ))^[k] _ (n + 1) - (fwdDiff (1 : ℕ))^[k] _ n = _
      rw [ih, ih]
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using
        binomial_difference ((K : ℤ) + (n : ℤ)) (s + (n : ℤ) + (k : ℤ))
  have h := fwdDiff_iter_eq_sum_shift (1 : ℕ)
    (fun m : ℕ => C((K : ℤ) + (m : ℤ), s + (m : ℤ))) kk 0
  rw [iter] at h
  simp only [Nat.cast_zero, add_zero, zero_add, nsmul_eq_mul, Nat.cast_id, mul_one,
    zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast] at h
  simpa only [binomial_nat] using h.symm

/-- Coefficients in the `(1+x)` basis, with integer subtraction in the lower index. -/
noncomputable def muCoeff (L b n : ℕ) : ℂ :=
  ∑ kk ∈ Icc n b, (-1 : ℂ) ^ (kk - n) *
    C((L : ℤ), (b : ℤ) - (kk : ℤ)) * C((kk : ℤ), (n : ℤ))

private theorem muCoeff_range (L b n : ℕ) :
    muCoeff L b n = ∑ kk ∈ range (b + 1), (-1 : ℂ) ^ (kk - n) *
      C((L : ℤ), (b : ℤ) - (kk : ℤ)) * C((kk : ℤ), (n : ℤ)) := by
  unfold muCoeff
  apply sum_subset
  · intro x hx
    simp only [mem_Icc] at hx
    simp only [mem_range]
    omega
  · intro x hx hxni
    simp only [mem_range] at hx
    simp only [mem_Icc, not_and, not_le] at hxni
    rw [binomial_above x (n : ℤ) (by omega), mul_zero]

/-- The finite binomial change of basis used in Zhu's associativity argument. -/
theorem mu_identity (K L b : ℕ) (s : ℤ) :
    ∑ k ∈ range (b + 1), C((K : ℤ), s + (k : ℤ)) *
        C((L : ℤ), (b : ℤ) - (k : ℤ)) =
      ∑ n ∈ range (b + 1), muCoeff L b n *
        C((K : ℤ) + (n : ℤ), s + (n : ℤ)) := by
  rw [show ∑ n ∈ range (b + 1), muCoeff L b n *
          C((K : ℤ) + (n : ℤ), s + (n : ℤ)) =
        ∑ n ∈ range (b + 1), ∑ kk ∈ range (b + 1),
          (-1 : ℂ) ^ (kk - n) * C((L : ℤ), (b : ℤ) - (kk : ℤ)) *
            C((kk : ℤ), (n : ℤ)) * C((K : ℤ) + (n : ℤ), s + (n : ℤ)) from
      sum_congr rfl (fun n _ => by rw [muCoeff_range, sum_mul]), sum_comm]
  refine sum_congr rfl (fun kk hkk => ?_)
  have hkkb : kk ≤ b := by have := mem_range.mp hkk; omega
  rw [show ∑ n ∈ range (b + 1),
          (-1 : ℂ) ^ (kk - n) * C((L : ℤ), (b : ℤ) - (kk : ℤ)) *
            C((kk : ℤ), (n : ℤ)) * C((K : ℤ) + (n : ℤ), s + (n : ℤ)) =
        C((L : ℤ), (b : ℤ) - (kk : ℤ)) *
          ∑ n ∈ range (b + 1), (-1 : ℂ) ^ (kk - n) * C((kk : ℤ), (n : ℤ)) *
            C((K : ℤ) + (n : ℤ), s + (n : ℤ)) from by
      rw [mul_sum]; exact sum_congr rfl (fun n _ => by ring)]
  rw [show ∑ n ∈ range (b + 1), (-1 : ℂ) ^ (kk - n) * C((kk : ℤ), (n : ℤ)) *
          C((K : ℤ) + (n : ℤ), s + (n : ℤ)) =
        ∑ n ∈ range (kk + 1), (-1 : ℂ) ^ (kk - n) * C((kk : ℤ), (n : ℤ)) *
          C((K : ℤ) + (n : ℤ), s + (n : ℤ)) from ?_]
  · rw [inner_lemma]; ring
  · symm
    apply sum_subset
    · intro x hx
      simp only [mem_range] at hx ⊢
      omega
    · intro x hx hxni
      simp only [mem_range, not_lt] at hx hxni
      rw [binomial_above kk (x : ℤ) (by omega), mul_zero, zero_mul]

#print axioms mu_identity

end D5.S3.VertexAlgebra.Lattice.ActualZhuMuIdentity
