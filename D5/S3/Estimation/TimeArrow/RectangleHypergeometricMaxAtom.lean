/- GID: D5/S3/Estimation/TimeArrow/RectangleHypergeometricMaxAtom
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/RectangleHypergeometricMaxAtom
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Balanced hypergeometric margins give a uniform inverse-square-root atom bound. -/

import D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
import Mathlib.Data.Finset.Max

open scoped BigOperators
open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace D5.S3.Estimation.TimeArrow.RectangleHypergeometricMaxAtom
noncomputable section

open private
  D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge.hypergeometric_balanced_central_atom
from D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge

open private
  D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments.kernel_normalization
from D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments


set_option quotPrecheck false in
local notation "W" => fun N R U t : ℕ => R.choose t * (N - R).choose (U - t)

set_option quotPrecheck false in
local notation "H" => fun N R U t : ℕ => if t ≤ U then
  ((R.choose t : ℝ) * ((N - R).choose (U - t) : ℝ)) / (N.choose U : ℝ) else 0

/-- Cross multiplication remains valid at the lower support boundary. -/
private theorem adjacent_cross {N R U t : ℕ} (hR : R ≤ N) (htR : t ≤ R)
    (htU : t < U) (hcell : U - t ≤ N - R + 1) :
    (W N R U (t + 1) : ℝ) * (t + 1) * ((N : ℝ) - R + t + 1 - U) =
      (W N R U t : ℝ) * ((R : ℝ) - t) * ((U : ℝ) - t) := by
  have ha := Nat.choose_succ_right_eq R t
  have hb := Nat.choose_succ_right_eq (N - R) (U - t - 1)
  have hk : U - t - 1 + 1 = U - t := by omega
  have hs : U - (t + 1) = U - t - 1 := by omega
  rw [hk] at hb
  have hc : U - t - 1 ≤ N - R := by omega
  have haR : (R.choose (t + 1) : ℝ) * (t + 1) =
      (R.choose t : ℝ) * ((R : ℝ) - t) := by
    have ha' : (R.choose (t + 1) : ℝ) * ((t + 1 : ℕ) : ℝ) =
        (R.choose t : ℝ) * ((R - t : ℕ) : ℝ) := by exact_mod_cast ha
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_sub htR] using ha'
  have hbR : ((N - R).choose (U - (t + 1)) : ℝ) * ((N : ℝ) - R + t + 1 - U) =
      ((N - R).choose (U - t) : ℝ) * ((U : ℝ) - t) := by
    have hb' : ((N - R).choose (U - t) : ℝ) * ((U - t : ℕ) : ℝ) =
        ((N - R).choose (U - t - 1) : ℝ) * ((N - R - (U - t - 1) : ℕ) : ℝ) := by
      exact_mod_cast hb
    rw [Nat.cast_sub htU.le, Nat.cast_sub hc, Nat.cast_sub hR,
      Nat.cast_sub (by omega : 1 ≤ U - t), Nat.cast_sub htU.le] at hb'
    rw [hs]
    push_cast at hb'
    nlinarith [hb']
  push_cast
  calc
    _ = ((R.choose (t + 1) : ℝ) * (t + 1)) *
        (((N - R).choose (U - (t + 1)) : ℝ) * ((N : ℝ) - R + t + 1 - U)) := by ring
    _ = ((R.choose t : ℝ) * ((R : ℝ) - t)) *
        (((N - R).choose (U - t) : ℝ) * ((U : ℝ) - t)) := by rw [haR, hbR]
    _ = _ := by ring

/-- Every positive maximizing atom lies between the two adjacent-ratio thresholds. -/
private theorem maximizing_thresholds {N R U m : ℕ} (hR : R ≤ N) (hU : U ≤ N)
    (hmR : m ≤ R) (hmU : m ≤ U) (hcell : U - m ≤ N - R)
    (hpos : 0 < W N R U m) (hmax : ∀ t ≤ U, W N R U t ≤ W N R U m) :
    ((N : ℝ) + 2) * m ≤ ((R : ℝ) + 1) * (U + 1) ∧
      ((R : ℝ) + 1) * (U + 1) ≤ ((N : ℝ) + 2) * (m + 1) := by
  have hposR : (0 : ℝ) < W N R U m := by exact_mod_cast hpos
  have hmRR : (m : ℝ) ≤ R := by exact_mod_cast hmR
  have hmUR : (m : ℝ) ≤ U := by exact_mod_cast hmU
  have hRN : (R : ℝ) ≤ N := by exact_mod_cast hR
  have hUN : (U : ℝ) ≤ N := by exact_mod_cast hU
  constructor
  · by_cases hm0 : m = 0
    · subst m; simp only [Nat.cast_zero, mul_zero]; positivity
    have hm1 : 1 ≤ m := by omega
    have hp := adjacent_cross hR (by omega : m - 1 ≤ R)
      (by omega : m - 1 < U) (by omega : U - (m - 1) ≤ N - R + 1)
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm1]; norm_num
    rw [Nat.sub_add_cancel hm1, hcast] at hp
    have hp' : (W N R U m : ℝ) * ((m : ℝ) * ((N : ℝ) - R + m - U)) =
        (W N R U (m - 1) : ℝ) * (((R : ℝ) - m + 1) * ((U : ℝ) - m + 1)) := by
      nlinarith [hp]
    have hprev : (W N R U (m - 1) : ℝ) ≤ W N R U m := by
      exact_mod_cast hmax (m - 1) (by omega)
    have hb : 0 ≤ ((R : ℝ) - m + 1) * ((U : ℝ) - m + 1) :=
      mul_nonneg (by linarith) (by linarith)
    have hx := mul_le_mul_of_nonneg_right hprev hb
    rw [← hp'] at hx
    have hy := le_of_mul_le_mul_left hx hposR
    nlinarith [hy]
  · by_cases hmEq : m = U
    · subst m; nlinarith
    have hmLt : m < U := by omega
    have hp := adjacent_cross hR hmR hmLt (by omega : U - m ≤ N - R + 1)
    have hnext : (W N R U (m + 1) : ℝ) ≤ W N R U m := by
      exact_mod_cast hmax (m + 1) (by omega)
    have hd : 0 ≤ (N : ℝ) - R + m + 1 - U := by
      have hc : ((U - m : ℕ) : ℝ) ≤ (N - R : ℕ) := by exact_mod_cast hcell
      rw [Nat.cast_sub hmU, Nat.cast_sub hR] at hc
      linarith
    have hx := mul_le_mul_of_nonneg_right hnext
      (mul_nonneg (by positivity : 0 ≤ (m : ℝ) + 1) hd)
    have hp' : (W N R U m : ℝ) * (((R : ℝ) - m) * ((U : ℝ) - m)) =
        (W N R U (m + 1) : ℝ) * (((m : ℝ) + 1) * ((N : ℝ) - R + m + 1 - U)) := by
      nlinarith [hp]
    rw [← hp'] at hx
    have hy := le_of_mul_le_mul_left hx hposR
    nlinarith [hy]

/-- A maximizing atom is within two of the mean, including tied modes. -/
private theorem maximizing_near_mean {N R U m : ℕ} (hN : 0 < N)
    (hR : R ≤ N) (hU : U ≤ N) (hmR : m ≤ R) (hmU : m ≤ U)
    (hcell : U - m ≤ N - R) (hpos : 0 < W N R U m)
    (hmax : ∀ t ≤ U, W N R U t ≤ W N R U m) :
    |(m : ℝ) - (U : ℝ) * R / N| ≤ 2 := by
  obtain ⟨hhi, hlo⟩ := maximizing_thresholds hR hU hmR hmU hcell hpos hmax
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hRN : (R : ℝ) ≤ N := by exact_mod_cast hR
  have hUN : (U : ℝ) ≤ N := by exact_mod_cast hU
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hmRN : (m : ℝ) ≤ N := by exact_mod_cast hmR.trans hR
  have hmRR : (m : ℝ) ≤ R := by exact_mod_cast hmR
  have hmUR : (m : ℝ) ≤ U := by exact_mod_cast hmU
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  apply abs_le.mpr
  constructor
  · have hmult : (U : ℝ) * R ≤ ((m : ℝ) + 2) * N := by
      nlinarith
    have hh : (U : ℝ) * R / N ≤ (m : ℝ) + 2 := (div_le_iff₀ hN0).mpr hmult
    linarith
  · have hmult : ((m : ℝ) - 2) * N ≤ (U : ℝ) * R := by
      nlinarith
    have hh : (m : ℝ) - 2 ≤ (U : ℝ) * R / N := (le_div_iff₀ hN0).mpr hmult
    linarith

/-- Each atom is at most one under the normalized, support-guarded kernel. -/
private theorem kernel_le_one {N R U t : ℕ} (hR : R ≤ N) (hU : U ≤ N) :
    H N R U t ≤ 1 := by
  by_cases ht : t ≤ U
  · have hs :=
      D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments.kernel_normalization hR hU
    have hl := Finset.single_le_sum (f := H N R U)
      (fun i _ => by dsimp; split_ifs <;> positivity)
      (show t ∈ range (U + 1) by exact mem_range.mpr (by omega))
    exact hl.trans_eq hs
  · simp only [if_neg ht]; norm_num

/-- For a fixed balance parameter, one constant controls every atom of
all hypergeometric tables, uniformly in both margins and population size. -/
theorem hypergeometric_balanced_max_atom (ρ : ℝ) (hρ : 0 < ρ) (hρhi : ρ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R U t : ℕ), 2 ≤ N → R ≤ N → U ≤ N →
      ρ * N ≤ R → (R : ℝ) ≤ (1 - ρ) * N →
      ρ * N ≤ U → (U : ℝ) ≤ (1 - ρ) * N →
      (if t ≤ U then
        ((R.choose t : ℝ) * ((N - R).choose (U - t) : ℝ)) / (N.choose U : ℝ)
      else 0) ≤ C / Real.sqrt N := by
  let C : ℝ := Real.sqrt (4 / ρ ^ 2) + Real.exp 4 / ((ρ ^ 2 / 2) ^ 2)
  have hρ2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N R U t hN hR hU hRlo hRhi hUlo hUhi
  have hNpos : 0 < N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  by_cases hlarge : 4 / ρ ^ 2 ≤ (N : ℝ)
  · obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (range (U + 1))
      (W N R U) (by simp : (range (U + 1)).Nonempty)
    have hmU : m ≤ U := Nat.lt_succ_iff.mp (mem_range.mp hm)
    have hmax' : ∀ u ≤ U, W N R U u ≤ W N R U m := by
      intro u hu; exact hmax u (mem_range.mpr (by omega))
    have htmin : U - min R U ≤ N - R := by omega
    have hminpos : 0 < W N R U (min R U) :=
      Nat.mul_pos (Nat.choose_pos (min_le_left _ _)) (Nat.choose_pos htmin)
    have hpos : 0 < W N R U m := hminpos.trans_le (hmax' _ (min_le_right _ _))
    have hmR : m ≤ R := Nat.choose_ne_zero_iff.mp
      (left_ne_zero_of_mul hpos.ne')
    have hcell : U - m ≤ N - R := Nat.choose_ne_zero_iff.mp
      (right_ne_zero_of_mul hpos.ne')
    have hnear := maximizing_near_mean hNpos hR hU hmR hmU hcell hpos hmax'
    have hw : 2 ≤ ρ ^ 2 * (N : ℝ) / 2 := by
      have hh := (div_le_iff₀ hρ2).mp hlarge
      nlinarith
    have hc :=
      D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge.hypergeometric_balanced_central_atom
        hNpos hR hU ρ 2 hρ
      hRlo hRhi hUlo hUhi hw hnear
    have hCm : Real.exp 4 / ((ρ ^ 2 / 2) ^ 2) ≤ C := by
      dsimp [C]; exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
    have hfinal : Real.exp 4 / ((ρ ^ 2 / 2) ^ 2 * Real.sqrt N) ≤ C / Real.sqrt N := by
      rw [← div_div]
      exact div_le_div_of_nonneg_right hCm hsqrt.le
    by_cases ht : t ≤ U
    · simp only [if_pos ht]
      have htm : (W N R U t : ℝ) ≤ W N R U m := by exact_mod_cast hmax' t ht
      have hden : (0 : ℝ) ≤ N.choose U := Nat.cast_nonneg _
      have hl := div_le_div_of_nonneg_right htm hden
      simp only [Nat.cast_mul] at hl
      exact hl.trans (hc.trans hfinal)
    · simp only [if_neg ht]; positivity
  · have hsmall : (N : ℝ) ≤ 4 / ρ ^ 2 := le_of_lt (lt_of_not_ge hlarge)
    have hsc := Real.sqrt_le_sqrt hsmall
    have hCt : Real.sqrt (N : ℝ) ≤ C := hsc.trans
      (by dsimp [C]; exact le_add_of_nonneg_right (by positivity))
    have hc : (1 : ℝ) ≤ C / Real.sqrt N := (le_div_iff₀ hsqrt).mpr (by simpa using hCt)
    exact (kernel_le_one hR hU).trans hc

end
end D5.S3.Estimation.TimeArrow.RectangleHypergeometricMaxAtom
