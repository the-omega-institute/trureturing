/- GID: D5/S3/Geometry/Convex/Cone/Alternative
   generality: G
   mirror-B: none(waiver:covered-by-monotone-interval-stability-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Tucker's key lemma and field-level theorem for finite families. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Source: https://github.com/TauCetiProject/TauCeti/blob/557dcf0fc5cc930bb3dd80a7f1aff6d8f2288647/TauCeti/Geometry/Convex/Cone/Alternative.lean
Modifications: local module imports and Lean 4.35 compatibility; only live field-level prerequisites retained.
License and applicable notices: docs/reports/licenses/TauCeti-LICENSE.txt and docs/reports/licenses/TauCeti-interval-stability.md.
-/
module

public import OmegaBuild.Commands

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Push

/-! Tucker's key lemma and field-level theorem for finite families. -/

compile_only_with_mathlib

@[expose] public section

namespace TauCeti

variable {ι K V : Type*}

section Field

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup V] [Module K V]

/-- Tucker's key lemma for the vectors indexed by `insert k s`. -/
private theorem exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at_of_finset [DecidableEq ι]
    (k : ι)
    (s : Finset ι) (a : ι → V) :
    ∃ x : ι → K, ∃ y : Module.Dual K V, (∀ j ∈ insert k s, 0 ≤ x j ∧ 0 ≤ y (a j)) ∧
      ∑ j ∈ insert k s, x j • a j = 0 ∧ 0 < x k + y (a k) := by
  induction s using Finset.induction_on generalizing a with
  | empty =>
    by_cases ha : a k = 0
    · exact ⟨Pi.single k 1, 0, by simp, by simp [ha], by simp⟩
    · obtain ⟨y, hy⟩ := Module.Projective.exists_dual_eq_one K ha
      exact ⟨0, y, by simp [hy], by simp, by simp [hy]⟩
  | insert n s hn ih =>
    by_cases hnk : n = k
    · subst hnk
      simpa only [Finset.insert_idem] using ih a
    have hn' : n ∉ insert k s := by simp [hn, hnk]
    have hne : ∀ j ∈ insert k s, j ≠ n := fun j hj h => hn' (h ▸ hj)
    rw [Finset.insert_comm]
    obtain ⟨x, y, hxy, hsum, hpos⟩ := ih a
    by_cases hy : 0 ≤ y (a n)
    · -- `y` is already nonnegative on the new vector: extend `x` by zero.
      refine ⟨Function.update x n 0, y, Finset.forall_mem_insert _ _ _ |>.2 ⟨by simp [hy],
        fun j hj => by simpa [Function.update_of_ne (hne j hj)] using hxy j hj⟩, ?_, ?_⟩
      · rw [Finset.sum_insert hn', Function.update_self, zero_smul, zero_add, ← hsum]
        exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (hne j hj)]
      · rwa [Function.update_of_ne (Ne.symm hnk)]
    · -- Otherwise project the old vectors along `a n` onto `ker y` and apply the induction
      -- hypothesis to the projected family `b j = a j + c j • a n`, where `y (b j) = 0`.
      push Not at hy
      set d := y (a n)
      have hd : d ≠ 0 := hy.ne
      set c : ι → K := fun j => -y (a j) / d
      have hc : ∀ j ∈ insert k s, 0 ≤ c j := fun j hj =>
        div_nonneg_of_nonpos (neg_nonpos.2 (hxy j hj).2) hy.le
      obtain ⟨u, z, huz, hsum', hpos'⟩ := ih fun j => a j + c j • a n
      set w : Module.Dual K V := z + (-z (a n) / d) • y
      have hw : ∀ j, w (a j) = z (a j + c j • a n) := fun j => by
        simp only [w, c, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
          smul_eq_mul]
        field_simp
      refine ⟨Function.update u n (∑ j ∈ insert k s, c j * u j), w, ?_, ?_, ?_⟩
      · refine Finset.forall_mem_insert _ _ _ |>.2 ⟨⟨?_, by simp [w, d, hd]⟩, fun j hj => ?_⟩
        · simpa using Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi) (huz i hi).1
        · simpa only [Function.update_of_ne (hne j hj), hw] using huz j hj
      · rw [Finset.sum_insert hn', Function.update_self, ← hsum', Finset.sum_smul]
        simp only [smul_add, smul_smul, Finset.sum_add_distrib]
        rw [add_comm]
        congr 1
        · exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (hne j hj)]
        · exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
      · simpa only [Function.update_of_ne (Ne.symm hnk), hw] using hpos'

/-- **Tucker's key lemma.** For a finite family of vectors `a j` and an index `k`, there are a
nonnegative linear relation `x` among the `a j` and a linear functional `y` that is nonnegative on
every `a j`, such that `x k + y (a k) > 0`: either `a k` occurs in a nonnegative relation, or some
functional nonnegative on the family is strictly positive on `a k`. -/
theorem exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at [Fintype ι] (a : ι → V) (k : ι) :
    ∃ x : ι → K, ∃ y : Module.Dual K V, 0 ≤ x ∧ ∑ j, x j • a j = 0 ∧ (∀ j, 0 ≤ y (a j)) ∧
      0 < x k + y (a k) := by
  classical
  obtain ⟨x, y, hxy, hsum, hpos⟩ :=
    exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at_of_finset (K := K) k
      (Finset.univ.erase k) a
  rw [Finset.insert_erase (Finset.mem_univ k)] at hxy hsum
  exact ⟨x, y, fun j => (hxy j (Finset.mem_univ j)).1, hsum,
    fun j => (hxy j (Finset.mem_univ j)).2, hpos⟩

/-- **Tucker's theorem.** For a finite family of vectors `a j` there are a nonnegative linear
relation `x` among the `a j` and a linear functional `y` that is nonnegative on every `a j`, such
that `x j + y (a j) > 0` for every `j`: each vector either occurs in the relation or is strictly
positive under `y`. -/
theorem exists_nonneg_sum_smul_eq_zero_and_forall_coeff_add_dual_pos [Fintype ι] (a : ι → V) :
    ∃ x : ι → K, ∃ y : Module.Dual K V, 0 ≤ x ∧ ∑ j, x j • a j = 0 ∧ (∀ j, 0 ≤ y (a j)) ∧
      ∀ j, 0 < x j + y (a j) := by
  -- Add up the relations and functionals given by Tucker's key lemma at every index.
  choose x y hx hsum hy hpos using
    exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at (K := K) a
  refine ⟨∑ k, x k, ∑ k, y k, Finset.sum_nonneg fun k _ ↦ hx k, ?_, fun j ↦ ?_, fun j ↦ ?_⟩
  · simp only [Finset.sum_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun k _ ↦ hsum k
  · rw [LinearMap.sum_apply]
    exact Finset.sum_nonneg fun k _ ↦ hy k j
  · rw [Finset.sum_apply, LinearMap.sum_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_pos' (fun k _ ↦ add_nonneg (hx k j) (hy k j)) ⟨j, Finset.mem_univ j, hpos j⟩

end Field

end TauCeti
