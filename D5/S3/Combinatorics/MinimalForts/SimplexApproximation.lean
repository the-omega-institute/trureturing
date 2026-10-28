/- GID: D5/S3/Combinatorics/MinimalForts/SimplexApproximation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MinimalForts/SimplexApproximation
   mirror-E: none(waiver:uniform-approximation-proof)
   anchors: [mathlib/module/Mathlib.Topology.Instances.AddCircle.DenseSubgroup]
   utility: none
   digest: Irrational rotation gives feasible nonnegative multiplicities on every sufficiently large integer simplex. -/

import D5.S3.Combinatorics.MinimalForts.RotationWindow
import Mathlib.Data.Finset.Max

/-! An interior linear target is approximated by nonnegative integer multiplicities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.SimplexApproximation

open Filter Topology

/-- The entire tail of integer orders admits a feasible approximation, for each tolerance. -/
theorem eventual_simplex_approximation (p b g c : ℝ) (hp : 0 < p) (hb : b < 0)
    (hg : 0 < g) (hgp : g < p) (hirr : Irrational (b / p))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∃ x y z : ℕ, x + y + z = k ∧
      |(x : ℝ) * b + (z : ℝ) * p - ((k : ℝ) * g + c)| < ε := by
  obtain ⟨M, hM⟩ := RotationWindow.uniform_real_window p b hp hirr ε hε
  let C := (3 * (M : ℝ)) * (p - b) + |c| + ε
  have hpg : 0 < p - g := sub_pos.mpr hgp
  obtain ⟨K, hK⟩ := exists_nat_gt (max ((|c| + ε) / g) (C / (p - g)))
  refine ⟨K, fun k hk => ?_⟩
  have hkr : (K : ℝ) ≤ k := by exact_mod_cast hk
  have hkg : |c| + ε < (k : ℝ) * g :=
    (div_lt_iff₀ hg).mp ((le_max_left _ _).trans_lt (hK.trans_le hkr))
  have hkp : C < (k : ℝ) * (p - g) :=
    (div_lt_iff₀ hpg).mp ((le_max_right _ _).trans_lt (hK.trans_le hkr))
  obtain ⟨x, z, hxlo, hxhi, herr⟩ := hM M le_rfl ((k : ℝ) * g + c)
  have hx0 : 0 ≤ x := le_trans (by positivity : (0 : ℤ) ≤ (M : ℤ)) hxlo
  have hxr0 : (0 : ℝ) ≤ x := by exact_mod_cast hx0
  have hxrb : (x : ℝ) ≤ 3 * (M : ℝ) := by exact_mod_cast hxhi
  have hxb : (x : ℝ) * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hxr0 hb.le
  have hclo : -|c| ≤ c := neg_abs_le c
  have hchi : c ≤ |c| := le_abs_self c
  have herrlo := (abs_lt.mp herr).1
  have herrhi := (abs_lt.mp herr).2
  have hzr0 : (0 : ℝ) ≤ z := by
    by_contra hz
    have hzp : (z : ℝ) * p < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hz) hp
    linarith
  have hz0 : 0 ≤ z := by exact_mod_cast hzr0
  have hpb : 0 ≤ p - b := by linarith
  have hxbnd := mul_le_mul_of_nonneg_right hxrb hpb
  have hsumr : (x : ℝ) + (z : ℝ) ≤ k := by
    dsimp [C] at hkp
    nlinarith
  have hsumi : x + z ≤ (k : ℤ) := by exact_mod_cast hsumr
  have hxn : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx0
  have hzn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
  have hsum : x.toNat + z.toNat ≤ k := by omega
  refine ⟨x.toNat, k - x.toNat - z.toNat, z.toNat, by omega, ?_⟩
  have hxx : (x.toNat : ℝ) = (x : ℝ) := by exact_mod_cast hxn
  have hzz : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hzn
  simpa only [hxx, hzz] using herr

/-- Feasible multiplicities can be chosen at every order with error tending to zero. -/
theorem simplex_approximation_sequence (p b g c : ℝ) (hp : 0 < p) (hb : b < 0)
    (hg : 0 < g) (hgp : g < p) (hirr : Irrational (b / p)) :
    ∃ x y z : ℕ → ℕ, (∀ k, x k + y k + z k = k) ∧
      Tendsto (fun k => (x k : ℝ) * b + (z k : ℝ) * p - ((k : ℝ) * g + c))
        atTop (𝓝 0) := by
  classical
  let A (k : ℕ) : Finset (ℕ × ℕ) :=
    ((Finset.range (k + 1)).product (Finset.range (k + 1))).filter
      (fun a => a.1 + a.2 ≤ k)
  let error (k : ℕ) (a : ℕ × ℕ) : ℝ :=
    |(a.1 : ℝ) * b + (a.2 : ℝ) * p - ((k : ℝ) * g + c)|
  have hmin (k : ℕ) : ∃ a ∈ A k, ∀ d ∈ A k, error k a ≤ error k d := by
    apply Finset.exists_min_image
    exact ⟨(0, 0), by simp [A]⟩
  choose a ha hleast using hmin
  refine ⟨fun k => (a k).1, fun k => k - (a k).1 - (a k).2,
    fun k => (a k).2, ?_, ?_⟩
  · intro k
    have hk : (a k).1 + (a k).2 ≤ k := (Finset.mem_filter.mp (ha k)).2
    change (a k).1 + (k - (a k).1 - (a k).2) + (a k).2 = k
    omega
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨K, hK⟩ := eventual_simplex_approximation p b g c hp hb hg hgp hirr ε hε
    refine ⟨K, fun k hk => ?_⟩
    obtain ⟨x, y, z, hsum, herr⟩ := hK k hk
    have hmem : (x, z) ∈ A k := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_range.mpr (by omega)
      · exact Finset.mem_range.mpr (by omega)
      · dsimp
        omega
    have hbound := hleast k (x, z) hmem
    have hsmall : error k (a k) < ε := hbound.trans_lt herr
    simpa only [error, Real.dist_eq, sub_zero] using hsmall

end D5.S3.Combinatorics.MinimalForts.SimplexApproximation
