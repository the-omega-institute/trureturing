/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothGrid
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothGrid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed smooth grids have vanishing cubic moments and fourth Wick defects. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveFiniteProbability
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveIntervalGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Fixed endpoint families are normalized before taking a finite common threshold. -/

open scoped BigOperators Topology
open Set Filter

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- Dividing every variable by the same scale divides its product moment by that scale's power. -/
theorem sieve_moment_div_scale {k : ℕ} (Q : ℕ+)
    (F : Fin k → ZMod (Q : ℕ) → ℝ) (c : ℝ) :
    sieveProductMoment Q (fun i x => F i x / c) = sieveProductMoment Q F / c ^ k := by
  simp only [sieveProductMoment, sieveExpectation, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.sum_div]
  ring

/-- The fourth Wick defect is homogeneous of degree four under a common division. -/
theorem sieve_defect_div_scale (Q : ℕ+)
    (F : Fin 4 → ZMod (Q : ℕ) → ℝ) (c : ℝ) :
    sieveWickDefect Q (fun i x => F i x / c) = sieveWickDefect Q F / c ^ 4 := by
  unfold sieveWickDefect sieveWickPairing
  simp_rw [show ∀ i j : Fin 4, ![(fun x => F i x / c), (fun x => F j x / c)] =
    (fun t x => (![F i, F j] : Fin 2 → ZMod (Q : ℕ) → ℝ) t x / c) from
      fun i j => by funext t x; fin_cases t <;> rfl]
  simp_rw [sieve_moment_div_scale]
  ring

private theorem sieve_normalized_error_bound (k : ℕ) (Q : ℕ+)
    (H C B r p z : ℝ) (hH : 2 ≤ H) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hp : 0 ≤ p) (hP : sieveDensity Q ≤ B * Real.log H)
    (hz : |z| ≤ C * H ^ ((k : ℝ) / 2 - r) * sieveDensity Q ^ p) :
    |z / sieveScale H ^ k| ≤
      (C * B ^ p) * ((Real.log H) ^ (p - (k : ℝ) / 2) / H ^ r) := by
  have hH0 : 0 < H := by linarith
  have hL : 0 < Real.log H := Real.log_pos (by linarith)
  have hP0 : 0 ≤ sieveDensity Q := by unfold sieveDensity; positivity
  have hA := (sieve_scale_power H hH k).1
  have hd : 0 < sieveScale H ^ k := pow_pos hA _
  rw [abs_div, abs_of_pos hd]
  calc
    _ ≤ (C * H ^ ((k : ℝ) / 2 - r) * (B * Real.log H) ^ p) / sieveScale H ^ k := by
      apply div_le_div_of_nonneg_right _ hd.le
      exact hz.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hP0 hP hp)
        (mul_nonneg hC (Real.rpow_nonneg hH0.le _)))
    _ = _ := by
      rw [(sieve_scale_power H hH k).2, momentScale,
        Real.mul_rpow hH0.le hL.le, Real.mul_rpow hB hL.le,
        Real.rpow_sub hH0, Real.rpow_sub hL]
      field_simp

private theorem sieve_log_power_rate (C r q : ℝ) (hr : 0 < r) :
    Tendsto (fun h : ℕ => C * ((Real.log h) ^ q / (h : ℝ) ^ r)) atTop (𝓝 0) := by
  simpa only [mul_zero, Function.comp_def] using
    ((isLittleO_log_rpow_rpow_atTop q hr).tendsto_div_nhds_zero.const_mul C).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

private theorem sieve_fixed_smoothed_third (hK : KuperbergSmoothed)
    (B δ : ℝ) (hB : 1 ≤ B) (hδ : 0 < δ) (a b : Fin 3 → ℝ)
    (hab : ∀ i, 0 ≤ a i ∧ a i ≤ b i) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h : ℕ in atTop, ∀ Q : ℕ+, Squarefree (Q : ℕ) → sieveDensity Q ≤ B * Real.log h →
      |sieveProductMoment Q (fun i => normalizedWeightedSum Q h (smoothedInterval δ hδ (a i) (b i)))| ≤ ε := by
  obtain ⟨C, hC, hbound⟩ := hK.third δ hδ a b hab
  have hrate := sieve_log_power_rate (C * B ^ (19/2 : ℝ))
    (1/21 : ℝ) ((19/2 : ℝ) - (3 : ℝ)/2) (by norm_num)
  filter_upwards [eventually_ge_atTop (3 : ℕ), hrate.eventually_le_const hε]
    with h hh hsmall Q hQ hP
  have hhR : (2 : ℝ) ≤ h := by exact_mod_cast (show 2 ≤ h by omega)
  change |sieveProductMoment Q (fun i x => sieveWeightedSum Q h (smoothedInterval δ hδ (a i) (b i)) x / sieveScale h)| ≤ ε
  rw [sieve_moment_div_scale]
  exact (sieve_normalized_error_bound 3 Q h C B (1/21) (19/2) _ hhR hC
    (by linarith) (by norm_num) hP (hbound Q hQ h hh)).trans hsmall

private theorem sieve_fixed_smoothed_fourth (hK : KuperbergSmoothed)
    (B δ : ℝ) (hB : 1 ≤ B) (hδ : 0 < δ) (a b : Fin 4 → ℝ)
    (hab : ∀ i, 0 ≤ a i ∧ a i ≤ b i) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h : ℕ in atTop, ∀ Q : ℕ+, Squarefree (Q : ℕ) → sieveDensity Q ≤ B * Real.log h →
      |sieveWickDefect Q (fun i => normalizedWeightedSum Q h (smoothedInterval δ hδ (a i) (b i)))| ≤ ε := by
  obtain ⟨C, hC, hbound⟩ := hK.fourth δ hδ a b hab
  have hrate := sieve_log_power_rate (C * B ^ (18 : ℝ))
    (1/28 : ℝ) ((18 : ℝ) - (4 : ℝ)/2) (by norm_num)
  filter_upwards [eventually_ge_atTop (3 : ℕ), hrate.eventually_le_const hε]
    with h hh hsmall Q hQ hP
  have hhR : (2 : ℝ) ≤ h := by exact_mod_cast (show 2 ≤ h by omega)
  change |sieveWickDefect Q (fun i x => sieveWeightedSum Q h (smoothedInterval δ hδ (a i) (b i)) x / sieveScale h)| ≤ ε
  rw [sieve_defect_div_scale]
  apply (sieve_normalized_error_bound 4 Q h C B (1/28) 18 _ hhR hC
    (by linarith) (by norm_num) hP ?_).trans hsmall
  simpa only [Nat.cast_ofNat, show (4 : ℝ) / 2 = 2 by norm_num, Real.rpow_ofNat]
    using hbound Q hQ h hh

/-- A fixed finite endpoint mesh admits one threshold for all its smoothed cubic moments. -/
theorem sieve_grid_smoothed_third (hK : KuperbergSmoothed) (M B δ : ℝ)
    (_hM : 1 ≤ M) (hB : 1 ≤ B) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h : ℕ in atTop, ∀ Q : ℕ+, Squarefree (Q : ℕ) → sieveDensity Q ≤ B * Real.log h →
    ∀ a b : Fin 3 → ℝ, admissible M a b →
      (∀ i, a i ∈ sieveEndpointGrid M δ ∧ b i ∈ sieveEndpointGrid M δ) →
      |sieveProductMoment Q (fun i => normalizedWeightedSum Q h (smoothedInterval δ hδ (a i) (b i)))| ≤ ε := by
  classical
  let s := Fintype.piFinset (fun _ : Fin 3 => sieveEndpointGrid M δ)
  have hf : ∀ᶠ h : ℕ in atTop, ∀ a ∈ s, ∀ b ∈ s, admissible M a b →
      ∀ Q : ℕ+, Squarefree (Q : ℕ) → sieveDensity Q ≤ B * Real.log h →
        |sieveProductMoment Q (fun i => normalizedWeightedSum Q h (smoothedInterval δ hδ (a i) (b i)))| ≤ ε := by
    apply (Filter.eventually_all_finset s).mpr
    intro a _ha
    apply (Filter.eventually_all_finset s).mpr
    intro b _hb
    by_cases hab : admissible M a b
    · filter_upwards [sieve_fixed_smoothed_third hK B δ hB hδ a b
        (fun i => ⟨(hab i).1, (hab i).2.1⟩) ε hε] with h hh _had
      exact hh
    · exact Filter.Eventually.of_forall (fun _ had => (hab had).elim)
  filter_upwards [hf] with h hh Q hQ hP a b hab hgrid
  exact hh a (Fintype.mem_piFinset.mpr (fun i => (hgrid i).1))
    b (Fintype.mem_piFinset.mpr (fun i => (hgrid i).2)) hab Q hQ hP

/-- A fixed finite endpoint mesh admits one threshold for all its smoothed fourth Wick defects. -/
theorem sieve_grid_smoothed_fourth (hK : KuperbergSmoothed) (M B δ : ℝ)
    (_hM : 1 ≤ M) (hB : 1 ≤ B) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h : ℕ in atTop, ∀ Q : ℕ+, Squarefree (Q : ℕ) → sieveDensity Q ≤ B * Real.log h →
    ∀ a b : Fin 4 → ℝ, admissible M a b →
      (∀ i, a i ∈ sieveEndpointGrid M δ ∧ b i ∈ sieveEndpointGrid M δ) →
      |sieveWickDefect Q (fun i => normalizedWeightedSum Q h (smoothedInterval δ hδ (a i) (b i)))| ≤ ε := by
  classical
  let s := Fintype.piFinset (fun _ : Fin 4 => sieveEndpointGrid M δ)
  have hf : ∀ᶠ h : ℕ in atTop, ∀ a ∈ s, ∀ b ∈ s, admissible M a b →
      ∀ Q : ℕ+, Squarefree (Q : ℕ) → sieveDensity Q ≤ B * Real.log h →
        |sieveWickDefect Q (fun i => normalizedWeightedSum Q h (smoothedInterval δ hδ (a i) (b i)))| ≤ ε := by
    apply (Filter.eventually_all_finset s).mpr
    intro a _ha
    apply (Filter.eventually_all_finset s).mpr
    intro b _hb
    by_cases hab : admissible M a b
    · filter_upwards [sieve_fixed_smoothed_fourth hK B δ hB hδ a b
        (fun i => ⟨(hab i).1, (hab i).2.1⟩) ε hε] with h hh _had
      exact hh
    · exact Filter.Eventually.of_forall (fun _ had => (hab had).elim)
  filter_upwards [hf] with h hh Q hQ hP a b hab hgrid
  exact hh a (Fintype.mem_piFinset.mpr (fun i => (hgrid i).1))
    b (Fintype.mem_piFinset.mpr (fun i => (hgrid i).2)) hab Q hQ hP

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
