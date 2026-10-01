/- GID: D5/S3/Arith/GoldenResource/ReferencePrefixDominance
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/ReferencePrefixDominance
   mirror-E: none(waiver:general-real-analysis)
   anchors: []
   utility: none
   digest: A strict finite geometric-prefix logarithmic comparison. -/

/- Content witness: the harmonic prefix minus the logarithm of
   the geometric prefix has a strictly positive derivative on (0,1), obtained
   by a finite-calculus calculation and the strict bound S_a(t) < a+1.
   There is one public theorem, with all derivative and algebra steps local.
   Direct frozen dependencies: none. Admission basis: escape-witness.
   Utility none: arbitrary real inputs and unbounded natural exponents; no
   certified instance, enumerator, checker or numerical reduction. -/

/- Predecessor search: no exact comparison found in D5 or pinned Mathlib
   db584cd6d46c92f209a44c0f1c829460d327499d. Mathlib's finite atanh bounds
   and logarithm power series have different conclusions. Scoped GitHub Lean
   searches for log/geom_sum and harmonic/geom_sum likewise gave no exact hit;
   b-mehta/exponential-ramsey supplies related atanh remainder estimates.
   The argument is repo-derived; no originality claim is made. -/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace D5.S3.Arith.GoldenResource.ReferencePrefixDominance

open Finset Real Set

/-- The logarithm of a finite geometric prefix is strictly below the matching
harmonic prefix for every ratio strictly between zero and one. -/
theorem log_geom_prefix_lt_harmonic_prefix {z : ℝ} {a : ℕ}
    (ha : 1 ≤ a) (hz : 0 < z) (hz1 : z < 1) :
    Real.log (∑ k ∈ range (a + 1), z ^ k) <
      ∑ k ∈ range a, z ^ (k + 1) / (k + 1) := by
  let S : ℝ → ℝ := fun t => (1 - t ^ (a + 1)) / (1 - t)
  let F : ℝ → ℝ := fun t =>
    (∑ k ∈ range a, t ^ (k + 1) / (k + 1)) - Real.log (S t)
  have hgeom (t : ℝ) (ht1 : t < 1) (n : ℕ) :
      (∑ k ∈ range n, t ^ k) = (1 - t ^ n) / (1 - t) := by
    rw [geom_sum_eq ht1.ne]
    apply (div_eq_div_iff (sub_ne_zero.mpr ht1.ne) (sub_ne_zero.mpr ht1.ne')).mpr
    ring
  have hSpos (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) : 0 < S t := by
    exact div_pos (sub_pos.mpr (pow_lt_one₀ ht ht1 (Nat.succ_ne_zero a)))
      (sub_pos.mpr ht1)
  have hderiv (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) :
      HasDerivAt F (t ^ a / (1 - t) * ((a + 1 : ℝ) / S t - 1)) t := by
    have hq : HasDerivAt
        (fun x : ℝ => ∑ k ∈ range a, x ^ (k + 1) / (k + 1))
        (∑ k ∈ range a, t ^ k) t := by
      apply HasDerivAt.fun_sum
      intro k hk
      apply ((hasDerivAt_pow (k + 1) t).div_const (k + 1 : ℝ)).congr_deriv
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      exact mul_div_cancel_left₀ (t ^ k) (show (k : ℝ) + 1 ≠ 0 by positivity)
    have hd : 1 - t ≠ 0 := (sub_pos.mpr ht1).ne'
    have hn : 1 - t ^ (a + 1) ≠ 0 :=
      (sub_pos.mpr (pow_lt_one₀ ht ht1 (Nat.succ_ne_zero a))).ne'
    have hs := (((hasDerivAt_pow (a + 1) t).const_sub 1).div
      ((hasDerivAt_id t).const_sub 1) hd).log (hSpos t ht ht1).ne'
    change HasDerivAt
      (fun x : ℝ => (∑ k ∈ range a, x ^ (k + 1) / (k + 1)) -
        Real.log ((1 - x ^ (a + 1)) / (1 - x))) _ t
    apply (hq.sub hs).congr_deriv
    rw [hgeom t ht1 a]
    dsimp only [S]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.div_apply, id_eq]
    field_simp [hd, hn]
    ring
  have hSlt (t : ℝ) (ht : 0 < t) (ht1 : t < 1) : S t < a + 1 := by
    dsimp only [S]
    rw [← hgeom t ht1 (a + 1)]
    have hsum : (∑ k ∈ range a, t ^ (k + 1)) < (∑ k ∈ range a, (1 : ℝ)) := by
      apply sum_lt_sum_of_nonempty ⟨0, mem_range.mpr ha⟩
      intro k hk
      exact pow_lt_one₀ ht.le ht1 (Nat.succ_ne_zero k)
    have hsplit := sum_range_succ' (fun k : ℕ => t ^ k) a
    rw [hsplit]
    simpa using add_lt_add_right hsum (1 : ℝ)
  have hmono : StrictMonoOn F (Icc (0 : ℝ) z) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 z)
    · intro t ht
      exact (hderiv t ht.1 (ht.2.trans_lt hz1)).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Ioo (0 : ℝ) z := by simpa only [interior_Icc] using ht
      rw [(hderiv t ht'.1.le (ht'.2.trans hz1)).deriv]
      apply mul_pos (div_pos (pow_pos ht'.1 a) (sub_pos.mpr (ht'.2.trans hz1)))
      exact sub_pos.mpr ((one_lt_div (hSpos t ht'.1.le (ht'.2.trans hz1))).mpr
        (hSlt t ht'.1 (ht'.2.trans hz1)))
  have hFz : F 0 < F z := hmono ⟨le_rfl, hz.le⟩ ⟨hz.le, le_rfl⟩ hz
  have hF0 : F 0 = 0 := by simp [F, S]
  rw [hF0] at hFz
  have hSz : S z = ∑ k ∈ range (a + 1), z ^ k := (hgeom z hz1 (a + 1)).symm
  change 0 < (∑ k ∈ range a, z ^ (k + 1) / (k + 1)) - Real.log (S z) at hFz
  rw [hSz] at hFz
  exact sub_pos.mp hFz

end D5.S3.Arith.GoldenResource.ReferencePrefixDominance

#print axioms D5.S3.Arith.GoldenResource.ReferencePrefixDominance.log_geom_prefix_lt_harmonic_prefix
