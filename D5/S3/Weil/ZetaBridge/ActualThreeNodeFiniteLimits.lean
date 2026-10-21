/- GID: D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: Both arithmetic branches have exact sorted finite limits for every fixed signed nonzero node. -/

import D5.S3.Weil.ZetaBridge.ActualThreeNodeFiniteSpectrum
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder Matrix Topology
open D5.S3.Weil.ZetaBridge
open Filter Set
open ActualThreeNodeFiniteAlgebra ActualThreeNodeFiniteEnergy ActualThreeNodeFiniteSpectrum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.ActualThreeNodeFiniteLimits

lemma roots_at_zero (g mu a : ℝ) (hh : 0 ≤ g ^ 2 + mu) :
    rhoPlus g mu a 0 = 6 * (g ^ 2 + mu) ∧ rhoMinus g mu a 0 = 0 := by
  have ht : evenTau g mu a 0 = 6 * (g ^ 2 + mu) := by
    unfold evenTau U ActualThreeNodeFiniteAlgebra.C
    ring
  have hd : evenRad g mu a 0 = (6 * (g ^ 2 + mu)) ^ 2 := by
    unfold evenRad U ActualThreeNodeFiniteAlgebra.C T
    ring
  have hp : 0 ≤ 6 * (g ^ 2 + mu) := by positivity
  simp only [rhoPlus, rhoMinus, ht, hd, Real.sqrt_sq hp]
  constructor <;> ring

/-- Continuity through the discriminant, with the correct positive large root. -/
lemma root_limits (g mu a : ℝ) (n : ℤ) (hh : 0 < g ^ 2 + mu) :
    Tendsto (fun N : ℕ => rhoPlus g mu a ((n : ℝ) / N)) atTop (𝓝 (6 * (g ^ 2 + mu))) ∧
    Tendsto (fun N : ℕ => rhoMinus g mu a ((n : ℝ) / N)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => O g mu a ((n : ℝ) / N)) atTop (𝓝 (4 * a ^ 2)) := by
  have hr := tendsto_const_div_atTop_nhds_zero_nat (n : ℝ)
  have hcp : Continuous (fun r : ℝ => rhoPlus g mu a r) := by
    unfold rhoPlus evenTau evenRad U ActualThreeNodeFiniteAlgebra.C T
    fun_prop
  have hcm : Continuous (fun r : ℝ => rhoMinus g mu a r) := by
    unfold rhoMinus evenTau evenRad U ActualThreeNodeFiniteAlgebra.C T
    fun_prop
  have hco : Continuous (fun r : ℝ => O g mu a r) := by unfold O; fun_prop
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Function.comp_def, (roots_at_zero g mu a hh.le).1] using (hcp.tendsto 0).comp hr
  · simpa only [Function.comp_def, (roots_at_zero g mu a hh.le).2] using (hcm.tendsto 0).comp hr
  · simpa [O, Function.comp_def] using (hco.tendsto 0).comp hr

/-- The determinant divided algebraically by r^2, without performing a division. -/
def detReduced (g mu a r : ℝ) : ℝ :=
  2 * a ^ 2 * (g ^ 2 + 4 * mu) / 3 +
  (4 * g * a * (g ^ 2 + mu) / 3) * r +
  (2 * a ^ 2 * g ^ 2 - 16 * a ^ 2 * (g ^ 2 + mu) / 9 +
    32 * (g ^ 2 + mu) ^ 2 / 45) * r ^ 2 +
  (4 * g * a * (g ^ 2 + mu) / 15) * r ^ 3 +
  (a ^ 2 * (g ^ 2 + 16 * mu) / 30) * r ^ 4

lemma determinant_factored (g mu a r : ℝ) :
    evenDet g mu a r = r ^ 2 * detReduced g mu a r := by
  rw [finite_determinant_identity]
  unfold detReduced
  ring

lemma scaled_det_two (g mu a : ℝ) (n : ℤ) (N : ℕ) (hN : N ≠ 0) :
    (N : ℝ) ^ 2 * evenDet g mu a ((n : ℝ) / N) =
      (n : ℝ) ^ 2 * detReduced g mu a ((n : ℝ) / N) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [determinant_factored]
  field_simp [hNr]
  <;> ring

lemma scaled_det_four_zero (g mu : ℝ) (n : ℤ) (N : ℕ) (hN : N ≠ 0) :
    (N : ℝ) ^ 4 * evenDet g mu 0 ((n : ℝ) / N) =
      32 * (g ^ 2 + mu) ^ 2 * (n : ℝ) ^ 4 / 45 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [exceptional_determinant_identity]
  field_simp [hNr]
  <;> ring

/-- Large-root division is justified on one eventual set by its positive limit. -/
lemma scaled_small_root_limit (g mu a : ℝ) (n : ℤ) (hh : 0 < g ^ 2 + mu) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * rhoMinus g mu a ((n : ℝ) / N)) atTop
      (𝓝 ((n : ℝ) ^ 2 * a ^ 2 * (g ^ 2 + 4 * mu) / (9 * (g ^ 2 + mu)))) := by
  have hp := (root_limits g mu a n hh).1
  have hpos : 0 < 6 * (g ^ 2 + mu) := by positivity
  have hep : ∀ᶠ N : ℕ in atTop, 0 < rhoPlus g mu a ((n : ℝ) / N) :=
    hp.eventually (Ioi_mem_nhds hpos)
  have hred : Continuous (fun r : ℝ => detReduced g mu a r) := by
    unfold detReduced
    fun_prop
  have hd : Tendsto (fun N : ℕ => (n : ℝ) ^ 2 * detReduced g mu a ((n : ℝ) / N)) atTop
      (𝓝 ((n : ℝ) ^ 2 * (2 * a ^ 2 * (g ^ 2 + 4 * mu) / 3))) := by
    simpa [detReduced] using
      (((hred.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat (n : ℝ))).const_mul ((n : ℝ) ^ 2))
  have hlim := hd.div hp hpos.ne'
  have hc : ((n : ℝ) ^ 2 * (2 * a ^ 2 * (g ^ 2 + 4 * mu) / 3)) /
      (6 * (g ^ 2 + mu)) =
      (n : ℝ) ^ 2 * a ^ 2 * (g ^ 2 + 4 * mu) / (9 * (g ^ 2 + mu)) := by
    field_simp [hh.ne']
    <;> ring
  rw [hc] at hlim
  apply hlim.congr'
  filter_upwards [hep, eventually_ge_atTop (1 : ℕ)] with N hpN hN
  have he := rhoMinus_eq_div g mu a ((n : ℝ) / N) hpN.ne'
  rw [he, ← mul_div_assoc, scaled_det_two g mu a n N (by omega)]
  rfl

lemma scaled_small_root_limit_zero (g mu : ℝ) (n : ℤ) (hh : 0 < g ^ 2 + mu) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 4 * rhoMinus g mu 0 ((n : ℝ) / N)) atTop
      (𝓝 (16 * (g ^ 2 + mu) * (n : ℝ) ^ 4 / 135)) := by
  have hp := (root_limits g mu 0 n hh).1
  have hpos : 0 < 6 * (g ^ 2 + mu) := by positivity
  have hep : ∀ᶠ N : ℕ in atTop, 0 < rhoPlus g mu 0 ((n : ℝ) / N) :=
    hp.eventually (Ioi_mem_nhds hpos)
  have hlim := (tendsto_const_nhds (x := 32 * (g ^ 2 + mu) ^ 2 * (n : ℝ) ^ 4 / 45)).div hp hpos.ne'
  have hc : (32 * (g ^ 2 + mu) ^ 2 * (n : ℝ) ^ 4 / 45) / (6 * (g ^ 2 + mu)) =
      16 * (g ^ 2 + mu) * (n : ℝ) ^ 4 / 135 := by
    field_simp [hh.ne']
    <;> ring
  rw [hc] at hlim
  apply hlim.congr'
  filter_upwards [hep, eventually_ge_atTop (1 : ℕ)] with N hpN hN
  rw [rhoMinus_eq_div g mu 0 ((n : ℝ) / N) hpN.ne', ← mul_div_assoc,
    scaled_det_four_zero g mu n N (by omega)]
  rfl

/-- Eventual exact ordering in the nonzero branch. The large pair is left as
max/min; its limiting values may be equal, and need not stabilize in order. -/
lemma nonzero_eventually_sorted (g mu a : ℝ) (n : ℤ) (hh : 0 < g ^ 2 + mu) (ha : a ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      finiteEigen g mu a ((n : ℝ) / N) =
        ![max (rhoPlus g mu a ((n : ℝ) / N)) (O g mu a ((n : ℝ) / N)),
          min (rhoPlus g mu a ((n : ℝ) / N)) (O g mu a ((n : ℝ) / N)),
          rhoMinus g mu a ((n : ℝ) / N)] := by
  rcases root_limits g mu a n hh with ⟨hp, hm, ho⟩
  have hA : 0 < 4 * a ^ 2 := by positivity
  have hd : Tendsto (fun N : ℕ => O g mu a ((n : ℝ) / N) -
      rhoMinus g mu a ((n : ℝ) / N)) atTop (𝓝 (4 * a ^ 2)) := by
    simpa only [sub_zero] using ho.sub hm
  filter_upwards [hd.eventually (Ioi_mem_nhds hA)] with N hN
  exact finite_sorted_eq g mu a ((n : ℝ) / N) (sub_pos.mp hN).le

/-- BOTH large-root limits, including 6h=4a^2, and the scaled small root. -/
theorem finite_nonzero_limits (g mu a : ℝ) (n : ℤ) (hh : 0 < g ^ 2 + mu) (ha : a ≠ 0) :
    Tendsto (fun N : ℕ => finiteEigen g mu a ((n : ℝ) / N) 0) atTop
      (𝓝 (max (6 * (g ^ 2 + mu)) (4 * a ^ 2))) ∧
    Tendsto (fun N : ℕ => finiteEigen g mu a ((n : ℝ) / N) 1) atTop
      (𝓝 (min (6 * (g ^ 2 + mu)) (4 * a ^ 2))) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * finiteEigen g mu a ((n : ℝ) / N) 2) atTop
      (𝓝 ((n : ℝ) ^ 2 * a ^ 2 * (g ^ 2 + 4 * mu) / (9 * (g ^ 2 + mu)))) := by
  rcases root_limits g mu a n hh with ⟨hp, hm, ho⟩
  have hs := nonzero_eventually_sorted g mu a n hh ha
  refine ⟨?_, ?_, ?_⟩
  · apply (hp.max ho).congr'
    filter_upwards [hs] with N hN
    rw [hN]
    simp
  · apply (hp.min ho).congr'
    filter_upwards [hs] with N hN
    rw [hN]
    simp
  · apply (scaled_small_root_limit g mu a n hh).congr'
    filter_upwards [hs] with N hN
    rw [hN]
    simp

/-- A single exterior cutoff works for the literal signed n, without transport. -/
lemma exterior_eventually (n : ℤ) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ |(n : ℝ)| < (N : ℝ) := by
  have hr : ∀ᶠ N : ℕ in atTop, |(n : ℝ)| < (N : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hr] with N hN hR
  exact ⟨hN, hR⟩

lemma zero_eventually_sorted (g mu : ℝ) {n : ℤ} (hn : n ≠ 0) (hh : 0 < g ^ 2 + mu) :
    ∀ᶠ N : ℕ in atTop,
      finiteEigen g mu 0 ((n : ℝ) / N) =
        ![rhoPlus g mu 0 ((n : ℝ) / N), O g mu 0 ((n : ℝ) / N),
          rhoMinus g mu 0 ((n : ℝ) / N)] := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  filter_upwards [exterior_eventually n] with N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have habs : |(n : ℝ) / N| < 1 := by
    rw [abs_div, abs_of_pos hNr]
    exact (div_lt_one hNr).mpr hN.2
  have hrat := abs_lt.mp habs
  have hprod : 0 < (1 - (n : ℝ) / N) * (1 + (n : ℝ) / N) :=
    mul_pos (sub_pos.mpr hrat.2) (by linarith [hrat.1])
  have hsq : ((n : ℝ) / N) ^ 2 ≤ 1 := by nlinarith only [hprod]
  exact exceptional_finite_sorted g mu ((n : ℝ) / N) hh
    (div_ne_zero hnR hNr.ne') hsq

/-- The exceptional middle eigenvalue has an exact scaled identity, N>0. -/
lemma zero_scaled_odd (g mu : ℝ) (n : ℤ) (N : ℕ) (hN : N ≠ 0) :
    (N : ℝ) ^ 2 * O g mu 0 ((n : ℝ) / N) = 4 * (g ^ 2 + mu) * (n : ℝ) ^ 2 / 3 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  unfold O
  field_simp [hNr]
  <;> ring

/-- The second arithmetic branch has its different, mandatory scales. -/
theorem finite_zero_limits (g mu : ℝ) {n : ℤ} (hn : n ≠ 0) (hh : 0 < g ^ 2 + mu) :
    Tendsto (fun N : ℕ => finiteEigen g mu 0 ((n : ℝ) / N) 0) atTop
      (𝓝 (6 * (g ^ 2 + mu))) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * finiteEigen g mu 0 ((n : ℝ) / N) 1) atTop
      (𝓝 (4 * (g ^ 2 + mu) * (n : ℝ) ^ 2 / 3)) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ 4 * finiteEigen g mu 0 ((n : ℝ) / N) 2) atTop
      (𝓝 (16 * (g ^ 2 + mu) * (n : ℝ) ^ 4 / 135)) := by
  have hs := zero_eventually_sorted g mu hn hh
  refine ⟨?_, ?_, ?_⟩
  · apply (root_limits g mu 0 n hh).1.congr'
    filter_upwards [hs] with N hN
    rw [hN]
    simp
  · apply (tendsto_const_nhds (x := 4 * (g ^ 2 + mu) * (n : ℝ) ^ 2 / 3)).congr'
    filter_upwards [hs, eventually_ge_atTop (1 : ℕ)] with N hN hpos
    rw [hN]
    simpa using (zero_scaled_odd g mu n N (by omega)).symm
  · apply (scaled_small_root_limit_zero g mu n hh).congr'
    filter_upwards [hs] with N hN
    rw [hN]
    simp

end D5.S3.Weil.ZetaBridge.ActualThreeNodeFiniteLimits
