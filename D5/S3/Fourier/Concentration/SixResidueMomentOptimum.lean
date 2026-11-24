/- GID: D5/S3/Fourier/Concentration/SixResidueMomentOptimum
   generality: I
   mirror-B: D5/B/S3/Fourier/Concentration/SixResidueMomentOptimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact smallest squared mass subject to two real moments on six residues. -/

import D5.S3.Fourier.Concentration.ClippedMomentWeights
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! Simultaneous lower bounds on the first two real character modes modulo six. -/

open Finset Matrix

noncomputable section

namespace D5.S3.Fourier.Concentration.SixResidueMomentOptimum

private def firstMode : Fin 6 → ℝ := ![1, 1 / 2, -1 / 2, -1, -1 / 2, 1 / 2]
private def secondMode : Fin 6 → ℝ := ![1, -1 / 2, -1 / 2, 1, -1 / 2, -1 / 2]

private def lowWeights (a : ℝ) : Fin 6 → ℝ :=
  ![(1 + 4 * a) / 6, 1 / 6, (1 - 2 * a) / 6, 1 / 6, (1 - 2 * a) / 6, 1 / 6]

private def highWeights (a : ℝ) : Fin 6 → ℝ :=
  ![a, (1 - a) / 3, 0, (1 - a) / 3, 0, (1 - a) / 3]

private def moment (w c : Fin 6 → ℝ) : ℝ := ∑ k, w k * c k
private def energy (w : Fin 6 → ℝ) : ℝ := ∑ k, w k ^ 2

private theorem sum_fin_six (f : Fin 6 → ℝ) :
    (∑ k, f k) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_succ]
  ring

private theorem firstMode_moment_gap (a t : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (u : Fin 6 → ℝ) (hu : ∀ k, u k = max 0 (1 - t * (1 - firstMode k)))
    (v : Fin 6 → ℝ) (hv : ∀ k, v k = u k / ∑ j, u j)
    (hfirst : moment v firstMode = a) : moment v secondMode < a := by
  let total := ∑ k, u k
  have hone : u 0 = 1 := by rw [hu]; norm_num [firstMode]
  have htotal : 0 < total := by
    have h := single_le_sum (s := (univ : Finset (Fin 6)))
      (f := u) (fun i _ => hu i ▸ le_max_left _ _) (mem_univ 0)
    change u 0 ≤ total at h
    rw [hone] at h
    linarith
  have hpos : 0 < t := by
    by_contra! hi
    have hU : ∀ k, u k = 1 - t * (1 - firstMode k) := by
      intro k
      rw [hu, max_eq_right]
      fin_cases k <;> norm_num [firstMode] <;> linarith
    have hnum : (∑ k, u k * firstMode k) = 3 * t := by
      simp only [sum_fin_six, hU]
      norm_num [firstMode]
      ring
    have hM : moment v firstMode = 3 * t / total := by
      simp only [moment, hv, div_mul_eq_mul_div, ← sum_div, hnum, total]
    have hnonpos : 3 * t / total ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) htotal.le
    linarith
  have ht2 : t < 2 := by
    by_contra! hi
    have hz₁ : u 1 = 0 := by
      rw [hu]
      apply max_eq_left
      norm_num [firstMode]
      linarith
    have hz₂ : u 2 = 0 := by
      rw [hu]
      apply max_eq_left
      norm_num [firstMode]
      linarith
    have hz₃ : u 3 = 0 := by
      rw [hu]
      apply max_eq_left
      norm_num [firstMode]
      linarith
    have hz₄ : u 4 = 0 := by
      rw [hu]
      apply max_eq_left
      norm_num [firstMode]
      linarith
    have hz₅ : u 5 = 0 := by
      rw [hu]
      apply max_eq_left
      norm_num [firstMode]
      linarith
    have hT : total = 1 := by simp [total, sum_fin_six, hone, hz₁, hz₂, hz₃, hz₄, hz₅]
    have hM : moment v firstMode = 1 := by
      simp only [moment, sum_fin_six, hv, show ∑ k, u k = 1 from hT,
        hone, hz₁, hz₂, hz₃, hz₄, hz₅]
      norm_num [firstMode]
    linarith
  have hd : moment v firstMode - moment v secondMode = v 1 + v 5 - 2 * v 3 := by
    norm_num [moment, sum_fin_six, firstMode, secondMode]
    ring
  have huv : u 1 = u 5 := by rw [hu, hu]; rfl
  have hlt : u 3 < u 1 := by
    rw [hu, hu]
    norm_num [firstMode]
    exact ⟨by linarith, by linarith⟩
  have hvlt : v 3 < v 1 := by rw [hv, hv]; exact div_lt_div_of_pos_right hlt htotal
  have hveq : v 1 = v 5 := by rw [hv, hv, huv]
  linarith

private theorem firstMode_cos (k : Fin 6) : firstMode k = Real.cos (Real.pi * (k.val : ℝ) / 3) := by
  fin_cases k <;> norm_num [firstMode]
  · rw [show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  · rw [show Real.pi * 4 / 3 = Real.pi / 3 + Real.pi by ring,
      Real.cos_add_pi, Real.cos_pi_div_three]
  · rw [show Real.pi * 5 / 3 = 2 * Real.pi - Real.pi / 3 by ring,
      Real.cos_two_pi_sub, Real.cos_pi_div_three]

private theorem secondMode_cos (k : Fin 6) : secondMode k = Real.cos (2 * Real.pi * (k.val : ℝ) / 3) := by
  fin_cases k <;> norm_num [secondMode]
  · rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  · rw [show 2 * Real.pi * 2 / 3 = Real.pi / 3 + Real.pi by ring,
      Real.cos_add_pi, Real.cos_pi_div_three]
  · rw [show 2 * Real.pi * 4 / 3 = (Real.pi - Real.pi / 3) + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_pi_sub, Real.cos_pi_div_three]
  · rw [show 2 * Real.pi * 5 / 3 = (Real.pi / 3 + Real.pi) + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_add_pi, Real.cos_pi_div_three]

private theorem aggregate_balance (f : ℝ → ℝ) :
    moment (fun k => f (firstMode k + secondMode k)) firstMode =
      moment (fun k => f (firstMode k + secondMode k)) secondMode := by
  norm_num [moment, sum_fin_six, firstMode, secondMode]
  ring

private def aggregate (i : Fin 6) : ℝ := firstMode i + secondMode i

private def aggregateRaw (t : ℝ) (i : Fin 6) : ℝ := max 0 (1 - t * (2 - aggregate i))

private def aggregateWeights (t : ℝ) (i : Fin 6) : ℝ :=
  aggregateRaw t i / ∑ j, aggregateRaw t j

private theorem aggregate_fin (i : Fin 6) :
    aggregate i = (![2, 0, -1, 0, -1, 0] : Fin 6 → ℝ) i := by
  fin_cases i <;> norm_num [aggregate, firstMode, secondMode]

private theorem aggregateRaw_pos (t : ℝ) :
    0 < ∑ i, aggregateRaw t i := by
  rw [sum_fin_six]
  have h₀ : aggregateRaw t 0 = 1 := by simp [aggregateRaw, aggregate_fin]
  rw [h₀]
  have h (i) : 0 ≤ aggregateRaw t i := le_max_left _ _
  linarith [h 1, h 2, h 3, h 4, h 5]

private theorem aggregateRaw_eq (t : ℝ) (i : Fin 6) :
    aggregateRaw t i = (![1, max 0 (1 - 2 * t), max 0 (1 - 3 * t),
      max 0 (1 - 2 * t), max 0 (1 - 3 * t), max 0 (1 - 2 * t)] : Fin 6 → ℝ) i := by
  fin_cases i <;> norm_num [aggregateRaw, aggregate_fin] <;> rw [mul_comm]

private theorem aggregate_moment_formula (t : ℝ) :
    moment (aggregateWeights t) aggregate =
      (2 - 2 * max 0 (1 - 3 * t)) / (1 + 3 * max 0 (1 - 2 * t) + 2 * max 0 (1 - 3 * t)) := by
  simp only [moment, aggregateWeights, sum_fin_six, aggregate_fin, aggregateRaw_eq]
  norm_num
  ring_nf

private theorem aggregateWeights_eq (a t : ℝ) (ht : t ≤ 1 / 2)
    (hm : moment (aggregateWeights t) aggregate = 2 * a) :
    aggregateWeights t = if a ≤ 1 / 2 then lowWeights a else highWeights a := by
  let S := ∑ i, aggregateRaw t i
  have hS : 0 < S := aggregateRaw_pos t
  have hraw₂ : 0 ≤ 1 - 2 * t := by linarith
  have hden : S = 1 + 3 * (1 - 2 * t) + 2 * max 0 (1 - 3 * t) := by
    simp only [S, sum_fin_six, aggregateRaw_eq]
    norm_num
    rw [max_eq_right hraw₂]
    ring
  have hnum :
      (2 - 2 * max 0 (1 - 3 * t)) = (2 * a) * S := by
    rw [aggregate_moment_formula, max_eq_right hraw₂, ← hden] at hm
    exact (div_eq_iff hS.ne').mp hm
  by_cases ht3 : t ≤ 1 / 3
  · have hraw₃ : 0 ≤ 1 - 3 * t := by linarith
    rw [max_eq_right hraw₃] at hden hnum
    have ha : a ≤ 1 / 2 := by
      have hle : 2 * a * S ≤ S := by linarith
      have h : 2 * a ≤ 1 := le_of_mul_le_mul_right (by simpa only [one_mul] using hle) hS
      linarith
    rw [ite_eq_left ha]
    have hmid : (1 - 2 * t) / S = 1 / 6 := by
      apply (div_eq_iff hS.ne').mpr
      linarith
    have hone : 1 / S = (1 + 4 * a) / 6 := by
      apply (div_eq_iff hS.ne').mpr
      linear_combination -hden / 6 + hnum / 3
    have hother : (1 - 3 * t) / S = (1 - 2 * a) / 6 := by
      apply (div_eq_iff hS.ne').mpr
      linear_combination -hden / 6 - hnum / 6
    funext i
    change aggregateRaw t i / S = lowWeights a i
    rw [aggregateRaw_eq]
    fin_cases i <;> simp [lowWeights, max_eq_right hraw₂, max_eq_right hraw₃, hone, hmid, hother]
  · have hraw₃ : 1 - 3 * t ≤ 0 := by linarith
    rw [max_eq_left hraw₃] at hden hnum
    have ha : ¬ a ≤ 1 / 2 := by
      intro ha
      have hle : 2 * a * S ≤ S := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (show 2 * a ≤ 1 by linarith) hS.le
      linarith
    rw [ite_eq_right ha]
    have hone : 1 / S = a := by
      apply (div_eq_iff hS.ne').mpr
      linear_combination hnum / 2
    have hmid : (1 - 2 * t) / S = (1 - a) / 3 := by
      apply (div_eq_iff hS.ne').mpr
      linear_combination -hden / 3 - hnum / 6
    funext i
    change aggregateRaw t i / S = highWeights a i
    rw [aggregateRaw_eq]
    fin_cases i <;> simp [highWeights, max_eq_right hraw₂, max_eq_left hraw₃, hone, hmid]

open D5.S3.Fourier.Concentration.ClippedMomentWeights

private theorem moment_aggregate (w : Fin 6 → ℝ) :
    moment w aggregate = moment w firstMode + moment w secondMode := by
  simp only [moment, aggregate, mul_add, sum_add_distrib]


private theorem six_deficit_identity (a : ℝ) (w : Fin 6 → ℝ)
    (hws : ∑ i, w i = 1) :
    let v := if a ≤ 1 / 2 then lowWeights a else highWeights a
    let m := moment w firstMode + moment w secondMode - 2 * a
    energy w - energy v - energy (w - v) =
      if a ≤ 1 / 2 then (2 * a / 3) * m
      else ((4 * a - 1) / 3) * m + (2 * a - 1) * (w 2 + w 4) := by
  dsimp only
  rw [sum_fin_six] at hws
  by_cases ha : a ≤ 1 / 2
  · simp only [ite_eq_left ha, energy, sum_fin_six, Pi.sub_apply, moment]
    norm_num [lowWeights, firstMode, secondMode]
    linear_combination hws / 3
  · simp only [ite_eq_right ha, energy, sum_fin_six, Pi.sub_apply, moment]
    norm_num [highWeights, firstMode, secondMode]
    linear_combination (2 * (1 - a) / 3) * hws

private theorem six_weight_optimum (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    let v := if a ≤ 1 / 2 then lowWeights a else highWeights a
    (∀ k, 0 ≤ v k) ∧ (∑ k, v k) = 1 ∧ moment v firstMode = a ∧ moment v secondMode = a ∧
      energy v = (if a ≤ 1 / 2 then (1 + 4 * a ^ 2) / 6 else a ^ 2 + (1 - a) ^ 2 / 3) ∧
      ∀ w : Fin 6 → ℝ, (∀ k, 0 ≤ w k) → (∑ k, w k) = 1 →
        2 * a ≤ moment w firstMode + moment w secondMode →
        energy (w - v) ≤ energy w - energy v := by
  dsimp only
  have hz : (∑ i, aggregate i) / Fintype.card (Fin 6) = 0 := by
    norm_num [sum_fin_six, aggregate_fin]
  have hC : ∃ j, aggregate j = 2 := ⟨0, by norm_num [aggregate_fin]⟩
  obtain ⟨t, _, hcut, _, hnn, hsum, hmoment, hgap⟩ :=
    ClippedMomentWeights.exists_clipped_moment_minimizer aggregate hC (a := 2 * a)
      (by linarith)
  have hb : t ≤ 1 / 2 := hcut.trans (sup'_le _ _ (by
    intro i _
    fin_cases i <;> norm_num [aggregate_fin]))
  have hm : moment (aggregateWeights t) aggregate = 2 * a := by
    simpa only [moment, aggregateWeights, aggregateRaw, hz,
      max_eq_right (mul_nonneg zero_le_two ha)] using hmoment
  have hv := aggregateWeights_eq a t hb hm
  rw [← hv]
  have hbalance := aggregate_balance (fun b => max 0 (1 - t * (2 - b)) /
    ∑ j, aggregateRaw t j)
  change moment (aggregateWeights t) firstMode = moment (aggregateWeights t) secondMode at hbalance
  have hm' := moment_aggregate (aggregateWeights t)
  have he : energy (aggregateWeights t) =
      if a ≤ 1 / 2 then (1 + 4 * a ^ 2) / 6 else a ^ 2 + (1 - a) ^ 2 / 3 := by
    rw [hv]
    split_ifs <;> norm_num [energy, sum_fin_six, lowWeights, highWeights] <;> ring
  refine ⟨hnn, hsum, by linarith, by linarith, he, ?_⟩
  intro w hw hws hwa
  exact (hgap w hws).2 hw (by rwa [← moment_aggregate] at hwa)

/-- Exact minimum squared mass under two real moment bounds on the six-element cycle.
The first-mode clipped optimizer misses the second bound at every interior threshold. -/
theorem six_two_mode_optimum (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    let c := fun k : Fin 6 => Real.cos (Real.pi * (k.val : ℝ) / 3)
    let d := fun k : Fin 6 => Real.cos (2 * Real.pi * (k.val : ℝ) / 3)
    let v : Fin 6 → ℝ := if a ≤ 1 / 2 then
      ![(1 + 4 * a) / 6, 1 / 6, (1 - 2 * a) / 6, 1 / 6, (1 - 2 * a) / 6, 1 / 6]
      else ![a, (1 - a) / 3, 0, (1 - a) / 3, 0, (1 - a) / 3]
    let square := fun x : ℝ => x ^ 2
    (∀ k, 0 ≤ v k) ∧ (∑ k, v k) = 1 ∧ (∑ k, v k * c k) = a ∧ (∑ k, v k * d k) = a ∧
      (∑ k, square (v k)) = (if a ≤ 1 / 2 then (1 + 4 * a ^ 2) / 6
        else a ^ 2 + (1 - a) ^ 2 / 3) ∧
      (∀ w : Fin 6 → ℝ, (∑ k, w k) = 1 →
        let m := (∑ k, w k * c k) + (∑ k, w k * d k) - 2 * a
        (∑ k, square (w k)) - (∑ k, square (v k)) - (∑ k, square (w k - v k)) =
          if a ≤ 1 / 2 then (2 * a / 3) * m
          else ((4 * a - 1) / 3) * m + (2 * a - 1) * (w 2 + w 4)) ∧
      (∀ w : Fin 6 → ℝ, (∀ k, 0 ≤ w k) → (∑ k, w k) = 1 →
        2 * a ≤ (∑ k, w k * c k) + ∑ k, w k * d k →
        (∑ k, square (w k - v k)) ≤ (∑ k, square (w k)) - ∑ k, square (v k)) ∧
      (0 < a → a < 1 → ∀ t : ℝ,
        let u := fun k : Fin 6 => max 0 (1 - t * (1 - c k))
        let p := fun k => u k / ∑ j, u j
        (∑ k, p k * c k) = a → (∑ k, p k * d k) < a) := by
  dsimp only
  simp_rw [← firstMode_cos, ← secondMode_cos]
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := six_weight_optimum a ha ha1
  refine ⟨h₁, h₂, h₃, h₄, h₅, six_deficit_identity a, h₆, ?_⟩
  intro hpos hone t
  exact firstMode_moment_gap a t hpos hone _ (fun _ => rfl) _ (fun _ => rfl)

end D5.S3.Fourier.Concentration.SixResidueMomentOptimum
