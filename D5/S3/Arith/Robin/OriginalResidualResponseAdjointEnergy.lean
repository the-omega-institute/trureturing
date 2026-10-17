/- GID: D5/S3/Arith/Robin/OriginalResidualResponseAdjointEnergy
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalResidualResponseAdjointEnergy
   mirror-E: none(waiver:finite-analytic-inequality)
   anchors: []
   utility: none
   digest: The same original response adjoint has a literal weighted-square energy lower bound with a collision-aware quadratic denominator. -/

import D5.S3.Arith.Robin.OriginalResidualPartialCellWeights
import D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate
import D5.S3.Arith.Robin.OriginalResidualResponseAdjoint
import Mathlib.Tactic

/-! Complete original-block energy, with repeated slots aggregated before squaring. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace D5.S3.Arith.Robin.OriginalResidualResponseAdjointEnergy

open D5.S3.Arith.Robin.OriginalResidualPartialCellWeights (w)
open D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate
  (response_four_point_gap)
open D5.S3.Arith.Robin.OriginalResidualResponseAdjoint
  (responseAdjointCoordinates responseAdjointResidual)

private theorem response_log_gap_pos {N : ℕ} (hN : 3 ≤ N) :
    0 < 1 - Real.log (2 : ℝ) / Real.log (N : ℝ) := by
  have hLN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog2N : Real.log (2 : ℝ) < Real.log (N : ℝ) :=
    Real.log_lt_log (by norm_num) (by exact_mod_cast (show 2 < N by omega))
  exact sub_pos.mpr ((div_lt_one hLN).mpr hlog2N)

/-- A collision-aware bound for the literal original adjoint energy.
The only hypothesis is N ≥ 3; the original arithmetic witness is derived. -/
theorem responseAdjoint_energy_lower_bound {N : ℕ} (hN : 3 ≤ N) :
    (1 - Real.log (2 : ℝ) / Real.log (N : ℝ)) ^ 2 /
        (24 * (N : ℝ) ^ 2 - 36 * (N : ℝ) + 14) ≤
      ∑ m ∈ Ico N (2 * N), w m * (responseAdjointResidual N m) ^ 2 := by
  classical
  let δ : ℝ := 1 - Real.log (2 : ℝ) / Real.log (N : ℝ)
  let K : ℝ := 24 * (N : ℝ) ^ 2 - 36 * (N : ℝ) + 14
  let E : ℕ → ℝ := responseAdjointResidual N
  let q : ℕ → ℝ := fun m => (m : ℝ) * ((m : ℝ) + 1)
  have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hδ : 0 < δ := response_log_gap_pos hN
  have hK : 0 < K := by
    dsimp only [K]
    nlinarith only [hNR, sq_nonneg ((N : ℝ) - 3)]
  obtain ⟨p, c, hNp, hpN, hNc, hcN, hpc, hgap⟩ := response_four_point_gap hN
  have hpm : p ∈ Ico N (2 * N) := mem_Ico.mpr ⟨by omega, hpN⟩
  have hcm : c ∈ Ico N (2 * N) := mem_Ico.mpr ⟨by omega, hcN⟩
  have hppm : p - 1 ∈ Ico N (2 * N) := mem_Ico.mpr ⟨by omega, by omega⟩
  have hcpm : c - 1 ∈ Ico N (2 * N) := mem_Ico.mpr ⟨by omega, by omega⟩
  let s : ℕ → ℝ := fun m =>
    (if m = c then 1 else 0) - (if m = c - 1 then 1 else 0) -
      (if m = p then 1 else 0) + (if m = p - 1 then 1 else 0)
  let D : ℝ := ∑ m ∈ Ico N (2 * N), (s m) ^ 2 * q m
  let T : ℝ := ∑ m ∈ Ico N (2 * N), w m * (E m) ^ 2

  have hL : (∑ m ∈ Ico N (2 * N), s m * E m) =
      (E c - E (c - 1)) - (E p - E (p - 1)) := by
    simp only [s, sub_mul, add_mul, ite_mul, one_mul, zero_mul,
      sum_sub_distrib, sum_add_distrib, sum_ite_eq',
      hcm, hcpm, hpm, hppm, if_true]
    ring
  have hδL : δ ≤ ∑ m ∈ Ico N (2 * N), s m * E m := by
    rw [hL]
    simpa only [δ, E, responseAdjointResidual] using
      hgap (responseAdjointCoordinates N 0) (responseAdjointCoordinates N 1)

  have hT : 0 ≤ T := by
    exact sum_nonneg fun m _ =>
      mul_nonneg (by unfold w; positivity) (sq_nonneg _)
  have hCS : (∑ m ∈ Ico N (2 * N), s m * E m) ^ 2 ≤ D * T := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (s := Ico N (2 * N))
      (r := fun m => s m * E m)
      (f := fun m => (s m) ^ 2 * q m)
      (g := fun m => w m * (E m) ^ 2)
    · intro m _
      exact mul_nonneg (sq_nonneg _) (by dsimp only [q]; positivity)
    · intro m _
      exact mul_nonneg (by unfold w; positivity) (sq_nonneg _)
    · intro m hm
      have hmpos : 0 < (m : ℝ) := by
        exact_mod_cast (show 0 < m by have := (mem_Ico.mp hm).1; omega)
      have hwq : q m * w m = 1 := by
        dsimp only [q, w]
        field_simp [hmpos.ne', (show (m : ℝ) + 1 ≠ 0 by positivity)]
      apply le_of_eq
      calc
        (s m * E m) ^ 2 = (s m) ^ 2 * (q m * w m) * (E m) ^ 2 := by
          rw [hwq]
          ring
        _ = ((s m) ^ 2 * q m) * (w m * (E m) ^ 2) := by ring

  -- This local arithmetic computation aggregates collisions BEFORE squaring.
  have hD : D ≤ K := by
    have hadj (j : ℕ) (hj : 1 ≤ j) (hjtop : j + 2 ≤ 2 * N)
        (hDj : D = q (j - 1) + 4 * q j + q (j + 1)) : D ≤ K := by
      have hqexact : q (j - 1) + 4 * q j + q (j + 1) =
          6 * (j : ℝ) * ((j : ℝ) + 1) + 2 := by
        simp only [q, Nat.cast_sub hj, Nat.cast_add, Nat.cast_one]
        ring
      have hjtopR : (j : ℝ) + 2 ≤ 2 * (N : ℝ) := by exact_mod_cast hjtop
      have hju : (j : ℝ) ≤ 2 * (N : ℝ) - 2 := by linarith
      have hprod : (j : ℝ) * ((j : ℝ) + 1) ≤
          (2 * (N : ℝ) - 2) * (2 * (N : ℝ) - 1) :=
        mul_le_mul hju (by linarith) (by positivity) (by linarith)
      calc
        D = 6 * (j : ℝ) * ((j : ℝ) + 1) + 2 := hDj.trans hqexact
        _ ≤ K := by dsimp only [K]; nlinarith only [hprod]

    by_cases hpcadj : p = c + 1
    · have hcnm : c + 1 ∈ Ico N (2 * N) := by simpa only [hpcadj] using hpm
      have hsquare (m : ℕ) : (s m) ^ 2 * q m =
          (if m = c - 1 then q m else 0) +
          (if m = c then 4 * q m else 0) +
          (if m = c + 1 then q m else 0) := by
        dsimp only [s]
        split_ifs <;> first | omega | ring
      have hDj : D = q (c - 1) + 4 * q c + q (c + 1) := by
        calc
          D = ∑ m ∈ Ico N (2 * N),
              ((if m = c - 1 then q m else 0) +
               (if m = c then 4 * q m else 0) +
               (if m = c + 1 then q m else 0)) := by
            exact sum_congr rfl fun m _ => hsquare m
          _ = _ := by
            simp only [sum_add_distrib, sum_ite_eq', hcpm, hcm, hcnm, if_true]
      exact hadj c (by omega) (by omega) hDj
    · by_cases hcpadj : c = p + 1
      · have hpnm : p + 1 ∈ Ico N (2 * N) := by simpa only [hcpadj] using hcm
        have hsquare (m : ℕ) : (s m) ^ 2 * q m =
            (if m = p - 1 then q m else 0) +
            (if m = p then 4 * q m else 0) +
            (if m = p + 1 then q m else 0) := by
          dsimp only [s]
          split_ifs <;> first | omega | ring
        have hDj : D = q (p - 1) + 4 * q p + q (p + 1) := by
          calc
            D = ∑ m ∈ Ico N (2 * N),
                ((if m = p - 1 then q m else 0) +
                 (if m = p then 4 * q m else 0) +
                 (if m = p + 1 then q m else 0)) := by
              exact sum_congr rfl fun m _ => hsquare m
            _ = _ := by
              simp only [sum_add_distrib, sum_ite_eq', hppm, hpm, hpnm, if_true]
        exact hadj p (by omega) (by omega) hDj
      · have hsquare (m : ℕ) : (s m) ^ 2 * q m =
            (if m = c then q m else 0) +
            (if m = c - 1 then q m else 0) +
            (if m = p then q m else 0) +
            (if m = p - 1 then q m else 0) := by
          dsimp only [s]
          split_ifs <;> first | omega | ring
        have hDj : D = q c + q (c - 1) + q p + q (p - 1) := by
          calc
            D = ∑ m ∈ Ico N (2 * N),
                ((if m = c then q m else 0) +
                 (if m = c - 1 then q m else 0) +
                 (if m = p then q m else 0) +
                 (if m = p - 1 then q m else 0)) := by
              exact sum_congr rfl fun m _ => hsquare m
            _ = _ := by
              simp only [sum_add_distrib, sum_ite_eq', hcm, hcpm, hpm, hppm, if_true]
        have hq (m : ℕ) (hm : m ∈ Ico N (2 * N)) :
            q m ≤ (2 * (N : ℝ) - 1) * (2 * (N : ℝ)) := by
          have hmup : (m : ℝ) + 1 ≤ 2 * (N : ℝ) := by
            exact_mod_cast (show m + 1 ≤ 2 * N by
              have := (mem_Ico.mp hm).2
              omega)
          exact mul_le_mul (by linarith) hmup (by positivity) (by linarith)
        have hcoarse : D ≤ 16 * (N : ℝ) ^ 2 - 8 * (N : ℝ) := by
          nlinarith only [hDj, hq c hcm, hq (c - 1) hcpm,
            hq p hpm, hq (p - 1) hppm]
        have hshift : 0 ≤ (N : ℝ) - 3 := by linarith
        dsimp only [K]
        nlinarith only [hcoarse, hshift, sq_nonneg ((N : ℝ) - 3)]

  have hδsq : δ ^ 2 ≤ (∑ m ∈ Ico N (2 * N), s m * E m) ^ 2 := by
    have hproduct : 0 ≤
        ((∑ m ∈ Ico N (2 * N), s m * E m) - δ) *
        ((∑ m ∈ Ico N (2 * N), s m * E m) + δ) :=
      mul_nonneg (sub_nonneg.mpr hδL) (by linarith)
    nlinarith only [hproduct]
  have hfinal : δ ^ 2 ≤ K * T :=
    hδsq.trans (hCS.trans (mul_le_mul_of_nonneg_right hD hT))
  change δ ^ 2 / K ≤ T
  exact (div_le_iff₀ hK).mpr (by simpa only [mul_comm] using hfinal)


end D5.S3.Arith.Robin.OriginalResidualResponseAdjointEnergy
