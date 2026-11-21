/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ThreeSpectrum/ExponentialChain
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A positivity criterion for bivariate exponential sums. -/

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-! Positivity of finite exponential sums from their annihilating differential chains. -/

open scoped BigOperators
open Set

noncomputable section

namespace RefinedBMV.ExponentialChain

def factors (roots : List ℝ) (rate : ℝ) : ℝ :=
  (roots.map fun root => rate - root).prod

private theorem sum_nonneg_of_prefix {ι : Type*} [Fintype ι]
    (rates : ι → ℝ) (roots : List ℝ) (weights : ι → ℝ)
    (hr : ∀ i, weights i ≠ 0 → rates i ∈ roots)
    (hjets : ∀ k < roots.length, 0 ≤ ∑ i, weights i * factors (roots.take k) (rates i))
    (x : ℝ) (hx : 0 ≤ x) : 0 ≤ ∑ i, weights i * Real.exp (rates i * x) := by
  induction roots generalizing weights x with
  | nil =>
    have hz (i : ι) : weights i = 0 := by
      by_contra hi
      exact List.not_mem_nil (hr i hi)
    simp [hz]
  | cons root roots ih =>
    let shifted (i : ι) := weights i * (rates i - root)
    have ht (k : ℕ) (hk : k < roots.length) :
        0 ≤ ∑ i, shifted i * factors (roots.take k) (rates i) := by
      have h := hjets (k + 1) (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk)
      simp only [List.take_succ_cons, factors, List.map_cons, List.prod_cons] at h ⊢
      simpa only [shifted, mul_assoc] using h
    -- Terms with the head rate vanish after the first factor.
    let f (t : ℝ) := ∑ i, weights i * Real.exp ((rates i - root) * t)
    have hm (i : ι) (hi : shifted i ≠ 0) : rates i ∈ roots := by
      refine (List.mem_cons.mp (hr i fun h => hi (by simp [shifted, h]))).resolve_left ?_
      exact fun h => hi (by simp [shifted, h])
    have hnext (t : ℝ) (ht₀ : 0 ≤ t) :=
      ih shifted hm ht t ht₀
    have hfactors (t : ℝ) (i : ι) :
        Real.exp ((rates i - root) * t) = Real.exp (-root * t) * Real.exp (rates i * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hderiv (t : ℝ) : HasDerivAt f
        (Real.exp (-root * t) * ∑ i, shifted i * Real.exp (rates i * t)) t := by
      have hpoint (i : ι) : HasDerivAt
          (fun t => weights i * Real.exp ((rates i - root) * t))
          (shifted i * Real.exp ((rates i - root) * t)) t := by
        have h := (((hasDerivAt_id' t).const_mul (rates i - root)).exp).const_mul (weights i)
        simpa only [mul_one, shifted, mul_assoc, mul_comm, mul_left_comm] using h
      have h := HasDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) => hpoint i
      convert h using 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hfactors]
      ring
    have hmono : MonotoneOn f (Ici (0 : ℝ)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (fun _ _ => (hderiv _).continuousAt.continuousWithinAt)
        (fun _ _ => (hderiv _).differentiableAt.differentiableWithinAt) ?_
      intro t htmem
      rw [(hderiv t).deriv]
      exact mul_nonneg (Real.exp_nonneg _) (hnext t (interior_subset htmem))
    have hzero : 0 ≤ f 0 := by
      simpa [f, factors] using hjets 0 (by simp)
    have hfx := hzero.trans (hmono (by simp) hx hx)
    have hfactor : f x = Real.exp (-root * x) * ∑ i, weights i * Real.exp (rates i * x) := by
      unfold f
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hfactors]
      ring
    rw [hfactor] at hfx
    exact nonneg_of_mul_nonneg_right hfx (Real.exp_pos _)

/-- Nonnegative initial values of both annihilating chains give a nonnegative
exponential sum on the nonnegative quadrant. The root lists may contain repetitions. -/
theorem sum_nonneg_of_mixed_prefix {ι κ : Type*} [Fintype ι] [Fintype κ]
    (rates : ι → ℝ) (rates' : κ → ℝ) (roots roots' : List ℝ)
    (hr : ∀ i, rates i ∈ roots) (hr' : ∀ j, rates' j ∈ roots')
    (weights : ι → κ → ℝ)
    (h : ∀ k < roots.length, ∀ l < roots'.length,
      0 ≤ ∑ i, ∑ j, weights i j * factors (roots.take k) (rates i) *
        factors (roots'.take l) (rates' j))
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ ∑ i, ∑ j, weights i j * Real.exp (rates i * x) * Real.exp (rates' j * y) := by
  let c (i : ι) := ∑ j, weights i j * Real.exp (rates' j * y)
  have houter (k : ℕ) (hk : k < roots.length) : 0 ≤ ∑ i, c i * factors (roots.take k) (rates i) := by
    let d (j : κ) := ∑ i, weights i j * factors (roots.take k) (rates i)
    have hd (l : ℕ) (hl : l < roots'.length) :
        0 ≤ ∑ j, d j * factors (roots'.take l) (rates' j) := by
      simp only [d, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact h k hk l hl
    have hs := sum_nonneg_of_prefix rates' roots' d (fun j _ => hr' j) hd y hy
    dsimp only [c] at *
    simp only [d, Finset.sum_mul] at hs ⊢
    rw [Finset.sum_comm] at hs
    convert hs using 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hs := sum_nonneg_of_prefix rates roots c (fun i _ => hr i) houter x hx
  simp only [c, Finset.sum_mul] at hs
  convert hs using 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem termwise_sum_nonneg_of_mixed_prefix {ι : Type*} [Fintype ι]
    (ratesX ratesY : ι → ℝ) (rootsX rootsY : List ℝ)
    (supportX : ∀ i, ratesX i ∈ rootsX) (supportY : ∀ i, ratesY i ∈ rootsY)
    (weights : ι → ℝ)
    (h : ∀ k < rootsX.length, ∀ l < rootsY.length,
      0 ≤ ∑ i, weights i * factors (rootsX.take k) (ratesX i) *
        factors (rootsY.take l) (ratesY i))
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ ∑ i, weights i * Real.exp (ratesX i * x + ratesY i * y) := by
  let c (i : ι) := weights i * Real.exp (ratesY i * y)
  have houter (k : ℕ) (hk : k < rootsX.length) :
      0 ≤ ∑ i, c i * factors (rootsX.take k) (ratesX i) := by
    have hi := sum_nonneg_of_prefix ratesY rootsY
      (fun i => weights i * factors (rootsX.take k) (ratesX i))
      (fun i _ => supportY i) (h k hk) y hy
    convert hi using 1
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [c]
    ring
  have hsum := sum_nonneg_of_prefix ratesX rootsX c
    (fun i _ => supportX i) houter x hx
  convert hsum using 1
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only [c]
  rw [Real.exp_add]
  ring

end RefinedBMV.ExponentialChain
