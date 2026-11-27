/- GID: D5/S3/Quantum/Semigroups/WuCubicEntropyRemainders
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicEntropyRemainders
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed Taylor bounds and the exact mass correction for Wu's cubic entropy. -/

import D5.S3.Divergence.ClassicalDPI
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import OmegaBuild.Commands

/-! The Gibbs-relative occupation entropy in the all-temperature Wu cubic proof
is the sum of the spectral remainders minus the remainder of the total mass.
The cubic terms retain the sign of the spectral and mass displacements. -/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

open Set
open scoped BigOperators Topology

namespace D5.S3.Quantum.Semigroups.WuCubicEntropyRemainders

open D5.S3.Divergence.ClassicalDPI (klDivergence)

private theorem iteratedDeriv_succ_eqOn_pos {f df ddf : ℝ → ℝ} {n : ℕ}
    (h : EqOn (iteratedDeriv n f) df (Ioi 0))
    (hd : ∀ y > 0, HasDerivAt df (ddf y) y) :
    EqOn (iteratedDeriv (n + 1) f) ddf (Ioi 0) := by
  intro y hy
  rw [iteratedDeriv_succ]
  have heq : iteratedDeriv n f =ᶠ[𝓝 y] df := by
    filter_upwards [Ioi_mem_nhds (show 0 < y from hy)] with z hz
    exact h hz
  exact ((hd y hy).congr_of_eventuallyEq heq).deriv

private theorem hasDerivAt_log_ratio {a y : ℝ} (ha : a ≠ 0) (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => Real.log (z / a)) y⁻¹ y := by
  apply ((Real.hasDerivAt_log hy.ne').sub_const (Real.log a)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with z hz
  exact Real.log_div (ne_of_gt hz) ha

private theorem fourth_order_remainder {f : ℝ → ℝ} {a x : ℝ} (hne : a ≠ x)
    (hf : ∀ y ∈ uIcc a x, ContDiffAt ℝ 4 f y) :
    ∃ y ∈ uIoo a x, f x -
      (f a + iteratedDeriv 1 f a * (x - a) +
        iteratedDeriv 2 f a * (x - a) ^ 2 / 2 +
        iteratedDeriv 3 f a * (x - a) ^ 3 / 6) =
      iteratedDeriv 4 f y * (x - a) ^ 4 / 24 := by
  have hc : ContDiffOn ℝ (3 + 1) f (uIcc a x) :=
    fun y hy => (hf y hy).contDiffWithinAt
  have hwithin (n : ℕ) (hn : n ≤ 4) :
      iteratedDerivWithin n f (uIcc a x) a = iteratedDeriv n f a :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      ((hf a left_mem_uIcc).of_le (by exact_mod_cast hn)) left_mem_uIcc
  have hpoly :
      taylorWithinEval f 3 (uIcc a x) a x =
        f a + iteratedDeriv 1 f a * (x - a) +
          iteratedDeriv 2 f a * (x - a) ^ 2 / 2 +
          iteratedDeriv 3 f a * (x - a) ^ 3 / 6 := by
    rw [taylorWithinEval_succ f 2, taylorWithinEval_succ f 1, taylorWithinEval_succ f 0,
      taylor_within_zero_eval, hwithin 1 (by decide), hwithin 2 (by decide),
      hwithin 3 (by decide)]
    norm_num [Nat.factorial, smul_eq_mul] <;> ring
  obtain ⟨y, hy, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 3) hne hc
  refine ⟨y, hy, ?_⟩
  rw [hpoly] at hrem
  simpa [Nat.factorial] using hrem

/-- The cubic spectral entropy remainder with the signed cubic term. -/
theorem cubic_entropy_remainder_le {x g : ℝ} (hx : 1 / 2 ≤ x) (hg : 1 / 2 ≤ g) :
    x ^ 3 * Real.log (x ^ 3 / g ^ 3) - x ^ 3 + g ^ 3 ≤
      (9 / 2) * g * (x - g) ^ 2 + (9 / 2) * (x - g) ^ 3 + (3 / 2) * (x - g) ^ 4 := by
  have hg0 : 0 < g := by linarith
  by_cases heq : g = x
  · subst x
    simp [div_self (pow_ne_zero 3 hg0.ne')]
  let f : ℝ → ℝ := fun y => y ^ 3 * Real.log (y ^ 3 / g ^ 3) - y ^ 3 + g ^ 3
  let L : ℝ → ℝ := fun y => Real.log (y / g)
  have hdL (y : ℝ) (hy : 0 < y) : HasDerivAt L y⁻¹ y :=
    hasDerivAt_log_ratio hg0.ne' hy
  have hlog (y : ℝ) : Real.log (y ^ 3 / g ^ 3) = 3 * L y := by
    rw [← div_pow, Real.log_pow] <;> rfl
  have h1 : EqOn (iteratedDeriv 1 f) (fun y => 9 * y ^ 2 * L y) (Ioi 0) := by
    apply iteratedDeriv_succ_eqOn_pos (n := 0) (df := f)
      (by intro y _; rw [iteratedDeriv_zero])
    intro y hy
    have hcube : HasDerivAt (fun z : ℝ => z ^ 3) (3 * y ^ 2) y := by
      simpa using hasDerivAt_pow 3 y
    have h := ((hcube.mul ((hdL y hy).const_mul 3)).sub hcube).add_const (g ^ 3)
    have hf : f = fun z => z ^ 3 * (3 * L z) - z ^ 3 + g ^ 3 := by
      funext z
      simp only [f, hlog]
    rw [hf]
    convert h using 1
    field_simp [hy.ne'] <;> ring
  have h2 : EqOn (iteratedDeriv 2 f) (fun y => 18 * y * L y + 9 * y) (Ioi 0) := by
    apply iteratedDeriv_succ_eqOn_pos h1
    intro y hy
    have hsquare : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
      simpa using hasDerivAt_pow 2 y
    have h := (hsquare.const_mul 9).mul (hdL y hy)
    convert h using 1
    field_simp [hy.ne'] <;> ring
  have h3 : EqOn (iteratedDeriv 3 f) (fun y => 18 * L y + 27) (Ioi 0) := by
    apply iteratedDeriv_succ_eqOn_pos h2
    intro y hy
    have h := (((hasDerivAt_id' y).const_mul 18).mul (hdL y hy)).add
      ((hasDerivAt_id' y).const_mul 9)
    convert h using 1
    field_simp [hy.ne'] <;> ring
  have h4 : EqOn (iteratedDeriv 4 f) (fun y => 18 / y) (Ioi 0) := by
    apply iteratedDeriv_succ_eqOn_pos h3
    intro y hy
    simpa only [div_eq_mul_inv] using ((hdL y hy).const_mul 18).add_const 27
  have hhalf {y : ℝ} (hy : y ∈ uIcc g x) : 1 / 2 ≤ y :=
    (le_min hg hx).trans hy.1
  have hsmooth (y : ℝ) (hy : y ∈ uIcc g x) : ContDiffAt ℝ 4 f y := by
    have hy0 : 0 < y := by linarith [hhalf hy]
    have hp : ContDiffAt ℝ 4 (fun z : ℝ => z ^ 3) y := by fun_prop
    have hl : ContDiffAt ℝ 4 Real.log (y ^ 3 / g ^ 3) :=
      Real.contDiffAt_log.2 (div_ne_zero (pow_ne_zero 3 hy0.ne') (pow_ne_zero 3 hg0.ne'))
    exact ((hp.mul (hl.comp y (hp.div_const (g ^ 3)))).sub hp).add contDiffAt_const
  obtain ⟨y, hy, hrem⟩ := fourth_order_remainder heq hsmooth
  have hyhalf := hhalf (uIoo_subset_uIcc_self hy)
  have hy0 : 0 < y := by linarith
  have hgL : L g = 0 := by simp [L]
  have hfg : f g = 0 := by simp [f, div_self (pow_ne_zero 3 hg0.ne')]
  rw [hfg, h1 hg0, h2 hg0, h3 hg0, h4 hy0] at hrem
  simp only [hgL] at hrem
  have hderiv_le : 18 / y ≤ 36 := by
    apply (div_le_iff₀ hy0).2
    linarith
  have hrem_le : (18 / y) * (x - g) ^ 4 / 24 ≤ 36 * (x - g) ^ 4 / 24 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hderiv_le (by positivity)) (by norm_num)
  change f x ≤ _
  linarith only [hrem, hrem_le]

/-- The signed lower Taylor bound for the mass correction, for either order of the masses. -/
theorem mass_entropy_remainder_ge {t t₀ : ℝ} (ht : 0 < t) (ht₀ : 0 < t₀) :
    (t - t₀) ^ 2 / (2 * t₀) - (t - t₀) ^ 3 / (6 * t₀ ^ 2) ≤
      t * Real.log (t / t₀) - t + t₀ := by
  by_cases heq : t₀ = t
  · subst t
    simp [ht₀.ne']
  let f : ℝ → ℝ := fun y => y * Real.log (y / t₀) - y + t₀
  have h1 : EqOn (iteratedDeriv 1 f) (fun y => Real.log (y / t₀)) (Ioi 0) := by
    apply iteratedDeriv_succ_eqOn_pos (n := 0) (df := f)
      (by intro y _; rw [iteratedDeriv_zero])
    intro y hy
    have h := (((hasDerivAt_id' y).mul (hasDerivAt_log_ratio ht₀.ne' hy)).sub
      (hasDerivAt_id' y)).add_const t₀
    convert h using 1
    field_simp [hy.ne'] <;> ring
  have h2 : EqOn (iteratedDeriv 2 f) (fun y => y⁻¹) (Ioi 0) :=
    iteratedDeriv_succ_eqOn_pos h1 fun _ hy => hasDerivAt_log_ratio ht₀.ne' hy
  have h3 : EqOn (iteratedDeriv 3 f) (fun y => -((y⁻¹) ^ 2)) (Ioi 0) :=
    iteratedDeriv_succ_eqOn_pos h2 fun _ hy => by
      simpa only [inv_pow] using hasDerivAt_inv hy.ne'
  have h4 : EqOn (iteratedDeriv 4 f) (fun y => 2 / y ^ 3) (Ioi 0) := by
    apply iteratedDeriv_succ_eqOn_pos h3
    intro y hy
    have h := ((hasDerivAt_inv hy.ne').pow 2).neg
    convert h using 1
    norm_num [div_eq_mul_inv, ← inv_pow] <;> ring
  have hpos {y : ℝ} (hy : y ∈ uIcc t₀ t) : 0 < y :=
    (lt_min ht₀ ht).trans_le hy.1
  have hsmooth (y : ℝ) (hy : y ∈ uIcc t₀ t) : ContDiffAt ℝ 4 f y := by
    have hi : ContDiffAt ℝ 4 (fun z : ℝ => z) y := by fun_prop
    have hl : ContDiffAt ℝ 4 Real.log (y / t₀) :=
      Real.contDiffAt_log.2 (div_ne_zero (hpos hy).ne' ht₀.ne')
    exact ((hi.mul (hl.comp y (hi.div_const t₀))).sub hi).add contDiffAt_const
  obtain ⟨y, hy, hrem⟩ := fourth_order_remainder heq hsmooth
  have hy0 := hpos (uIoo_subset_uIcc_self hy)
  have hf₀ : f t₀ = 0 := by simp [f, ht₀.ne']
  rw [hf₀, h1 ht₀, h2 ht₀, h3 ht₀, h4 hy0] at hrem
  simp only [div_self ht₀.ne', Real.log_one] at hrem
  have hpoly :
      0 + 0 * (t - t₀) + t₀⁻¹ * (t - t₀) ^ 2 / 2 +
        (-((t₀⁻¹) ^ 2)) * (t - t₀) ^ 3 / 6 =
      (t - t₀) ^ 2 / (2 * t₀) - (t - t₀) ^ 3 / (6 * t₀ ^ 2) := by
    field_simp [ht₀.ne'] <;> ring
  rw [hpoly] at hrem
  have hnonneg : 0 ≤ (2 / y ^ 3) * (t - t₀) ^ 4 / 24 := by positivity
  change _ ≤ f t
  linarith only [hrem, hnonneg]

/-- Normalizing two finite positive mass functions removes exactly their scalar
total-mass remainder from the sum of their pointwise remainders. -/
theorem mass_mul_klDivergence_eq {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    let A := ∑ i, a i
    let B := ∑ i, b i
    A * klDivergence (fun i => a i / A) (fun i => b i / B) =
      (∑ i, (a i * Real.log (a i / b i) - a i + b i)) -
        (A * Real.log (A / B) - A + B) := by
  intro A B
  have hA : 0 < A := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hB : 0 < B := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have hpoint (i : ι) :
      A * (a i / A * Real.log ((a i / A) / (b i / B))) =
        a i * Real.log (a i / b i) - a i * Real.log (A / B) := by
    have hlog :
        Real.log ((a i / A) / (b i / B)) =
          Real.log (a i / b i) - Real.log (A / B) := by
      rw [Real.log_div (div_ne_zero (ha i).ne' hA.ne') (div_ne_zero (hb i).ne' hB.ne'),
        Real.log_div (ha i).ne' hA.ne', Real.log_div (hb i).ne' hB.ne',
        Real.log_div (ha i).ne' (hb i).ne', Real.log_div hA.ne' hB.ne']
      ring
    rw [hlog, ← mul_assoc, mul_div_cancel₀ _ hA.ne']
    ring
  rw [klDivergence, Finset.mul_sum]
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  change (∑ i, a i * Real.log (a i / b i)) - A * Real.log (A / B) =
    (∑ i, a i * Real.log (a i / b i)) - A + B - (A * Real.log (A / B) - A + B)
  ring

/-- The occupation entropy upper bound for arbitrary spectral roots at least one half.
The reference mass is the sum of the reference cubes. -/
theorem mass_normalized_cubic_entropy_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (x g : ι → ℝ) (hx : ∀ i, 1 / 2 ≤ x i) (hg : ∀ i, 1 / 2 ≤ g i) :
    let T := ∑ i, x i ^ 3
    let T₀ := ∑ i, g i ^ 3
    T * klDivergence (fun i => x i ^ 3 / T) (fun i => g i ^ 3 / T₀) ≤
      (∑ i, ((9 / 2) * g i * (x i - g i) ^ 2 + (9 / 2) * (x i - g i) ^ 3 +
        (3 / 2) * (x i - g i) ^ 4)) -
        (T - T₀) ^ 2 / (2 * T₀) + (T - T₀) ^ 3 / (6 * T₀ ^ 2) := by
  intro T T₀
  have hxpos (i : ι) : 0 < x i ^ 3 := pow_pos (by linarith [hx i]) 3
  have hgpos (i : ι) : 0 < g i ^ 3 := pow_pos (by linarith [hg i]) 3
  have hT : 0 < T := Finset.sum_pos (fun i _ => hxpos i) Finset.univ_nonempty
  have hT₀ : 0 < T₀ := Finset.sum_pos (fun i _ => hgpos i) Finset.univ_nonempty
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => cubic_entropy_remainder_le (hx i) (hg i))
  have hmass := mass_entropy_remainder_ge hT hT₀
  rw [mass_mul_klDivergence_eq (fun i => x i ^ 3) (fun i => g i ^ 3) hxpos hgpos]
  linarith only [hsum, hmass]

end D5.S3.Quantum.Semigroups.WuCubicEntropyRemainders
