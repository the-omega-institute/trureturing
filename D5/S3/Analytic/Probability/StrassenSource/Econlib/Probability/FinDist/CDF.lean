/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.FinDist.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# CDF of a finite distribution

The cumulative distribution function of a `FinDist α` over a finite linear order: `FinDist.cdf d a`
is the total mass at or below the cutoff `a`. This file holds the construction and the
distribution-free API (evaluation forms, bounds, monotonicity, point masses). The FOSD order theory
built on the CDF is in `Econlib.Probability.Order.FOSD.*`; closed-form CDFs of concrete
distributions are kept with those distributions under `Econlib.Probability.Distributions.*`.

## Main definitions

* `FinDist.cdf` — total mass at or below a cutoff.

## Main statements

* `FinDist.cdf_eq_sum_ite` — indicator-sum evaluation form.
* `FinDist.cdf_eq_sum_range` — over `Fin (n + 1)`, the CDF as a `Finset.range` sum of the masses.
* `FinDist.cdf_nonneg`, `FinDist.cdf_le_one`, `FinDist.cdf_mono` — bounds and monotonicity.
* `FinDist.cdf_max` — the CDF reaches `1` at the maximum element.
* `FinDist.pure_cdf` — CDF of a point mass.
* `FinDist.pure_min_cdf` — the point mass at the minimum has CDF identically `1`.

## Tags

probability, finite distributions, cumulative distribution function, cdf
-/

@[expose] public section

open Finset BigOperators

namespace Econlib.Probability

namespace FinDist

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- CDF of a finite distribution at a cutoff: The total mass at or below `a`. -/
noncomputable def cdf (d : FinDist α) (a : α) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun y => y ≤ a), d x

/-- CDF as the filter-sum of masses at or below the cutoff. -/
@[simp] lemma cdf_eq_sum (d : FinDist α) (a : α) :
    d.cdf a = ∑ x ∈ Finset.univ.filter (fun y => y ≤ a), d x := rfl

/-- CDF as a sum of indicators over the whole space.

This is the `Fin.sum_univ_*`/`norm_num`-friendly evaluation form (contrast `cdf_eq_sum`, the filter
form). -/
@[simp] lemma cdf_eq_sum_ite (d : FinDist α) (a : α) :
    d.cdf a = ∑ x, if x ≤ a then d x else 0 := by
  rw [cdf_eq_sum, Finset.sum_filter]

/-- Over `Fin (n + 1)`, the CDF at cutoff `k` is the `Finset.range`-sum of the masses up to `k`,
read through any `ℕ`-indexed formula `g` for the pmf. Used for closed-form CDFs of distributions
whose pmf is given by an explicit formula in the outcome index. -/
lemma cdf_eq_sum_range {n : ℕ} (d : FinDist (Fin (n + 1))) {g : ℕ → ℝ}
    (hg : ∀ i : Fin (n + 1), d.pmf i = g i) (k : Fin (n + 1)) :
    d.cdf k = ∑ i ∈ Finset.range ((k : ℕ) + 1), g i := by
  -- Cutting `range (n + 1)` at `k ≤ n` is the same as truncating to `range (k + 1)`.
  have hfilter : Finset.range ((k : ℕ) + 1) =
      (Finset.range (n + 1)).filter (fun i => i ≤ (k : ℕ)) := by
    have hk := k.isLt
    ext a
    simp only [Finset.mem_range, Finset.mem_filter, Nat.lt_succ_iff]
    omega
  rw [cdf_eq_sum_ite, hfilter, Finset.sum_filter,
    ← Fin.sum_univ_eq_sum_range (fun i => if i ≤ (k : ℕ) then g i else 0) (n + 1)]
  exact Finset.sum_congr rfl fun x _ =>
    if_congr (Iff.symm Fin.val_fin_le) ((pmf_eq_coe d x).symm.trans (hg x)) rfl

/-- CDF of a pure (point-mass) distribution. -/
lemma pure_cdf (s a : α) :
    (FinDist.pure s : FinDist α).cdf a = if s ≤ a then 1 else 0 := by
  have hpure : ∀ x, (FinDist.pure s : FinDist α) x = if s = x then 1 else 0 := fun _ => rfl
  simp only [FinDist.cdf_eq_sum, hpure, Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- The CDF is nonnegative. -/
lemma cdf_nonneg (d : FinDist α) (a : α) : 0 ≤ d.cdf a :=
  sum_nonneg fun i _ => d.nonneg i

/-- The CDF is bounded above by `1`. -/
lemma cdf_le_one (d : FinDist α) (a : α) : d.cdf a ≤ 1 := by
  calc d.cdf a
      ≤ ∑ i, d.pmf i :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i _ _ => d.nonneg i
    _ = 1 := d.sum_one

/-- The CDF is monotone in the cutoff. -/
lemma cdf_mono (d : FinDist α) : Monotone d.cdf :=
  fun _ _ ha => sum_le_sum_of_subset_of_nonneg
    (fun i hi => by simp only [mem_filter, mem_univ, true_and] at hi ⊢; exact le_trans hi ha)
    fun i _ _ => d.nonneg i

/-- The CDF reaches `1` at the maximum element of the (nonempty) state space. -/
lemma cdf_max [Nonempty α] (d : FinDist α) :
    d.cdf (univ.max' univ_nonempty) = 1 := by
  -- Everything is at or below the maximum, so the filter is all of `univ`.
  have hfilt : univ.filter (fun y : α => y ≤ univ.max' univ_nonempty) = univ :=
    filter_true_of_mem fun a _ => le_max' univ a (mem_univ a)
  simp only [cdf, hfilt]; exact d.sum_one

/-- The point mass at the minimum element has CDF identically `1`. -/
lemma pure_min_cdf [Nonempty α] (a : α) :
    (FinDist.pure (univ.min' univ_nonempty)).cdf a = 1 := by
  rw [pure_cdf, if_pos (min'_le univ a (mem_univ a))]

end FinDist

end Econlib.Probability
