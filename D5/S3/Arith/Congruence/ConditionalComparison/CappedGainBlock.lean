/- GID: D5/S3/Arith/Congruence/ConditionalComparison/CappedGainBlock
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: The complete one-block analytic bridge. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/CappedGainBlock.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainDistortion
import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainRearrangement

/-!
# The complete one-block analytic bridge

This connects the actual distorted law to the fixed full-label majorant.
The elementary pre-update prefix bounds are hypotheses here; the prime-tree
construction supplies them in the covering-system application.
-/

namespace Erdos7.CappedGain

variable {ι : Type*} [DecidableEq ι]

theorem admissible_cap {p t r : ℚ} (hp : 3 ≤ p) (ht : t ≤ p - 3)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / (p - 2 - t)) : r * beta p 1 ≤ 1 := by
  have hc : 1 ≤ p - 2 - t := by linarith
  have hc0 : 0 < p - 2 - t := by linarith
  have hdiv : 1 / (p - 2 - t) ≤ (1 : ℚ) := (div_le_one hc0).mpr hc
  exact (mul_le_mul_of_nonneg_left (beta_one_le (by linarith)) hr0).trans
    (by simpa using hr.trans hdiv)

def block (p t : ℚ) (D : ℕ) (depth : ι → ℕ)
    (future : ι → Prop) [DecidablePred future] (w : ι → ℚ)
    (F : Finset ι → ℚ) (A : Finset ι) : ℚ :=
  lift (p - 2) t (fun S ↦ F (depthLe depth 0 S)) (gain p D depth F)
    (modularLoad w A) (A.filter future)

theorem block_supermodular {p t : ℚ} (hp : 3 ≤ p) (ht : t ≤ p - 3)
    (D : ℕ) (depth : ι → ℕ) (future : ι → Prop) [DecidablePred future]
    (w : ι → ℚ) (hw : ∀ x, 0 ≤ w x) (hw0 : ∀ x, future x → w x = 0)
    {F : Finset ι → ℚ} (hF : Supermodular F) (hInc : Increasing F) :
    Supermodular (block p t D depth future w F) := by
  apply lift_supermodular (by linarith) future w hw hw0
    (fun S ↦ F (depthLe depth 0 S)) (gain p D depth F)
    (gain_nonneg (by linarith) D depth hInc)
    (gain_increasing (by linarith) D depth hF hInc)
  intro r hr0 hr
  exact phi_supermodular D depth (by linarith) hr0 (admissible_cap hp ht hr0 hr) hF

theorem block_increasing {p t : ℚ} (hp : 3 ≤ p) (ht : t ≤ p - 3)
    (D : ℕ) (depth : ι → ℕ) (future : ι → Prop) [DecidablePred future]
    (w : ι → ℚ) (hw : ∀ x, 0 ≤ w x)
    {F : Finset ι → ℚ} (hInc : Increasing F) :
    Increasing (block p t D depth future w F) := by
  apply lift_increasing (by linarith) future w hw
    (fun S ↦ F (depthLe depth 0 S)) (gain p D depth F)
    (gain_nonneg (by linarith) D depth hInc)
  intro r hr0 hr
  exact phi_increasing D depth (by linarith) hr0 (admissible_cap hp ht hr0 hr) hInc

theorem block_empty {p t : ℚ} (hp : 3 ≤ p) (ht0 : 0 ≤ t) (ht : t ≤ p - 3)
    (D : ℕ) (depth : ι → ℕ) (future : ι → Prop) [DecidablePred future]
    (w : ι → ℚ) {F : Finset ι → ℚ} (hF0 : F ∅ = 0) :
    block p t D depth future w F ∅ = 0 := by
  simp only [block, modularLoad, Finset.sum_empty, Finset.filter_empty]
  exact lift_zero (by linarith) ht0 _ _ (by simpa using hF0) (gain_empty _ _ _ _)

theorem block_nonneg {p t : ℚ} (hp : 3 ≤ p) (ht0 : 0 ≤ t) (ht : t ≤ p - 3)
    (D : ℕ) (depth : ι → ℕ) (future : ι → Prop) [DecidablePred future]
    (w : ι → ℚ) (hw : ∀ x, 0 ≤ w x)
    {F : Finset ι → ℚ} (hInc : Increasing F) (hF0 : F ∅ = 0) (A : Finset ι) :
    0 ≤ block p t D depth future w F A := by
  have h := block_increasing hp ht D depth future w hw hInc (Finset.empty_subset A)
  rwa [block_empty hp ht0 ht D depth future w hF0] at h

/-- The charge and future expectation under one actual normalized update are
bounded by the capped-gain lift. No independence of label events is assumed. -/
theorem physical_block_bound {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (ending : Ω → Prop) [DecidablePred ending]
    (S : Finset ι) (active : Ω → Finset ι) (hactive : ∀ ω, active ω ⊆ S)
    (depth : ι → ℕ) {D : ℕ} (hdepth : ∀ x ∈ S, depth x ≤ D)
    {p P θ t L : ℚ} (hp : 3 ≤ p) (hpP : p ≤ P)
    (ht0 : 0 ≤ t) (ht : t ≤ p - 3) (hθ : P - 2 ≤ θ) (hL : 0 ≤ L)
    (hload : θ * μ.prob ending ≤ L)
    (hprefix : ∀ x ∈ S, depth x ≠ 0 →
      μ.prob (fun ω ↦ x ∈ active ω) ≤ beta P (depth x) / θ)
    {F : Finset ι → ℚ} (hF : Supermodular F) (hInc : Increasing F) :
    let ν := μ.distort ending (t / θ)
      (by have hθ0 : 0 < θ := by linarith
          exact div_nonneg ht0 hθ0.le)
      (by have hθ0 : 0 < θ := by linarith
          exact (div_lt_one hθ0).mpr (by linarith))
    ν.prob ending + ν.expect (fun ω ↦ F (active ω)) ≤
      lift (p - 2) t (fun T ↦ F (depthLe depth 0 T)) (gain p D depth F) L S := by
  dsimp only
  have hθ0 : 0 < θ := by linarith
  have hδ0 : 0 ≤ t / θ := div_nonneg ht0 hθ0.le
  have hδ1 : t / θ < 1 := (div_lt_one hθ0).mpr (by linarith)
  let ν := μ.distort ending (t / θ) hδ0 hδ1
  have hpaid : ν.prob ending ≤ charge (p - 2) t L := by
    rw [show ν.prob ending = thresholdMass (t / θ) (μ.prob ending) from
      μ.distort_prob ending _ hδ0 hδ1]
    exact thresholdMass_le_load ht0 (by linarith) (by linarith) hload
  have hcap := admissible_cap hp ht (rho_pos (by linarith : t < p - 2) L).le
    (rho_le (by linarith : t < p - 2) L)
  have hfuture : ν.expect (fun ω ↦ F (active ω)) ≤
      phi p (rho (p - 2) t L) D depth F S := by
    apply depth_rearrangement ν S active hactive depth hdepth (by linarith)
      (rho_pos (by linarith) L).le hcap hF hInc
    intro x hx hd
    have h1 := distorted_prefix_le μ ending (fun ω ↦ x ∈ active ω)
      ht0 (by linarith : t < P - 2) hθ (beta_nonneg (by linarith) (depth x))
      hload (hprefix x hx hd)
    have h2 := prime_prefix_cap_mono (by linarith : 1 ≤ p) hpP
      (le_min ht0 hL) (by linarith [min_le_left t L]) (depth x)
    have h2' : beta P (depth x) * rho (P - 2) t L ≤
        rho (p - 2) t L * beta p (depth x) := by
      unfold rho
      linear_combination h2
    exact h1.trans h2'
  have hmajor := lift_majorizes (p - 2) t (fun T ↦ F (depthLe depth 0 T))
    (gain p D depth F) L S
  dsimp [phi] at hfuture
  change ν.prob ending + ν.expect (fun ω ↦ F (active ω)) ≤ _
  linarith

end Erdos7.CappedGain
