/- GID: D5/S1/Words/Mechanical/MechanicalReadoutAtomicSeries
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalReadoutAtomicSeries
   mirror-E: none(waiver:actual-mechanical-atomic-series)
   anchors: []
   utility: none
   digest: Geometric mechanical readouts have an atomic floor expansion. -/

import D5.S1.Words.Mechanical.MechanicalReadoutOrder
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries

open Set Finset Filter
open scoped BigOperators
open D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.MechanicalReadoutOrder

/-- Abel summation turns the actual geometric mechanical letters into a floor
series. Its coefficients have exactly unit total mass when each time-k floor
is resolved into its k possible threshold atoms. The threshold-count identity
then identifies the readout with the corresponding atomic distribution sum. -/
theorem geometric_readout_floor_series_and_mass
    (r alpha x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : alpha ∈ Icc (0 : ℝ) 1) (hx : x ∈ Ico (0 : ℝ) 1) :
    geometricReadout r alpha x =
      ∑' j : ℕ, (1 - r) ^ 2 * r ^ j * (⌊x + ((j + 1 : ℕ) : ℝ) * alpha⌋ : ℝ) ∧
    (∑' j : ℕ, (1 - r) ^ 2 * r ^ j * ((j + 1 : ℕ) : ℝ)) = 1 ∧
    geometricReadout r alpha x =
      ∑' j : ℕ, (1 - r) ^ 2 * r ^ j *
        (∑ i ∈ range (j + 1),
          if (((i + 1 : ℕ) : ℝ) - x) / ((j + 1 : ℕ) : ℝ) ≤ alpha then
            (1 : ℝ) else 0) := by
  let q : ℕ → ℝ := fun j => (1 - r) * r ^ j
  let F : ℕ → ℝ := fun n => (⌊x + (n : ℝ) * alpha⌋ : ℝ)
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hq0 (j : ℕ) : 0 ≤ q j :=
    mul_nonneg (sub_nonneg.mpr hr1.le) (pow_nonneg hr0 j)
  have hF0 : F 0 = 0 := by
    have hfloor : ⌊x⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr hx
    simp [F, hfloor]
  have hF (n : ℕ) : 0 ≤ F n ∧ F n ≤ n := by
    have hnonneg : x ≤ x + (n : ℝ) * alpha := by
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg' n) ha.1)
    have hfloor0 : (0 : ℤ) ≤ ⌊x + (n : ℝ) * alpha⌋ := by
      rw [← Int.floor_eq_zero_iff.mpr hx]
      exact Int.floor_mono hnonneg
    have hmul : (n : ℝ) * alpha ≤ n := by
      calc
        (n : ℝ) * alpha ≤ (n : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left ha.2 (Nat.cast_nonneg' n)
        _ = n := by ring
    have hlt : x + (n : ℝ) * alpha < (n : ℝ) + 1 := by linarith [hx.2]
    have hfloorN : ⌊x + (n : ℝ) * alpha⌋ ≤ (n : ℤ) :=
      Int.floor_le_iff.mpr (by exact_mod_cast hlt)
    constructor
    · change (0 : ℝ) ≤ (⌊x + (n : ℝ) * alpha⌋ : ℝ)
      exact_mod_cast hfloor0
    · change (⌊x + (n : ℝ) * alpha⌋ : ℝ) ≤ n
      exact_mod_cast hfloorN
  have hletter (j : ℕ) :
      (lowerMechanicalLetter alpha x j : ℝ) = F (j + 1) - F j := by
    dsimp [F, lowerMechanicalLetter]
    push_cast
    ring
  have hgeom : Summable (fun j : ℕ => (((j + 1 : ℕ) : ℝ) * r ^ j)) := by
    simpa using (summable_choose_mul_geometric_of_norm_lt_one 1 hrnorm)
  have hbound : Summable (fun j : ℕ => q j * ((j + 1 : ℕ) : ℝ)) := by
    simpa [q, mul_assoc, mul_left_comm, mul_comm] using hgeom.mul_left (1 - r)
  have hA : Summable (fun j : ℕ => q j * F (j + 1)) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hbound
    · intro j
      exact mul_nonneg (hq0 j) (hF (j + 1)).1
    · intro j
      exact mul_le_mul_of_nonneg_left (hF (j + 1)).2 (hq0 j)
  have hB : Summable (fun j : ℕ => q j * F j) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hbound
    · intro j
      exact mul_nonneg (hq0 j) (hF j).1
    · intro j
      have hcast : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ j
      exact (mul_le_mul_of_nonneg_left (hF j).2 (hq0 j)).trans
        (mul_le_mul_of_nonneg_left hcast (hq0 j))
  have hBshift :
      (∑' j : ℕ, q j * F j) = ∑' j : ℕ, q (j + 1) * F (j + 1) := by
    have h := hB.sum_add_tsum_nat_add 1
    simpa [hF0] using h.symm
  have hAsh : Summable (fun j : ℕ => q (j + 1) * F (j + 1)) := by
    exact (summable_nat_add_iff 1).mpr hB
  have hdrop (j : ℕ) : q j - q (j + 1) = (1 - r) ^ 2 * r ^ j := by
    dsimp [q]
    rw [pow_succ]
    ring
  have hseries : geometricReadout r alpha x =
      ∑' j : ℕ, (q j - q (j + 1)) * F (j + 1) := by
    calc
      geometricReadout r alpha x =
          ∑' j : ℕ, q j * (F (j + 1) - F j) := by
            apply tsum_congr
            intro j
            rw [hletter]
      _ = (∑' j : ℕ, q j * F (j + 1)) - (∑' j : ℕ, q j * F j) := by
            simp_rw [mul_sub]
            exact hA.tsum_sub hB
      _ = (∑' j : ℕ, q j * F (j + 1)) -
            (∑' j : ℕ, q (j + 1) * F (j + 1)) := by rw [hBshift]
      _ = ∑' j : ℕ, (q j - q (j + 1)) * F (j + 1) := by
            rw [← hA.tsum_sub hAsh]
            simp_rw [sub_mul]
  have hmass : (∑' j : ℕ, (1 - r) ^ 2 * r ^ j * ((j + 1 : ℕ) : ℝ)) = 1 := by
    have hsum := tsum_choose_mul_geometric_of_norm_lt_one 1 hrnorm
    have hsum' : (∑' j : ℕ, (((j + 1 : ℕ) : ℝ) * r ^ j)) =
        1 / (1 - r) ^ 2 := by simpa using hsum
    calc
      (∑' j : ℕ, (1 - r) ^ 2 * r ^ j * ((j + 1 : ℕ) : ℝ)) =
          (1 - r) ^ 2 * ∑' j : ℕ, (((j + 1 : ℕ) : ℝ) * r ^ j) := by
            rw [← tsum_mul_left]
            congr 1
            funext j
            ring
      _ = 1 := by
        rw [hsum']
        have hne : 1 - r ≠ 0 := by linarith
        field_simp [hne]
  have hcount (k : ℕ) (hk : 0 < k) :
      (⌊x + (k : ℝ) * alpha⌋ : ℝ) =
        ∑ i ∈ range k,
          if (((i + 1 : ℕ) : ℝ) - x) / (k : ℝ) ≤ alpha then (1 : ℝ) else 0 := by
    let t : ℝ := x + (k : ℝ) * alpha
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have ht0 : 0 ≤ t := add_nonneg hx.1 (mul_nonneg hkpos.le ha.1)
    have htlt : t < (k : ℝ) + 1 := by
      dsimp [t]
      have hmul : (k : ℝ) * alpha ≤ k := by
        calc
          (k : ℝ) * alpha ≤ (k : ℝ) * 1 := mul_le_mul_of_nonneg_left ha.2 hkpos.le
          _ = k := by ring
      linarith [hx.2]
    have hmle : Nat.floor t ≤ k := by
      have hlt : Nat.floor t < k + 1 :=
        (Nat.floor_lt ht0).mpr (by exact_mod_cast htlt)
      omega
    have hfloorNat : (⌊t⌋ : ℝ) = (Nat.floor t : ℝ) := by
      have hfloor0 : (0 : ℤ) ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht0
      have hi : (⌊t⌋ : ℤ) = ((Nat.floor t : ℕ) : ℤ) := by
        calc
          (⌊t⌋ : ℤ) = ((⌊t⌋.toNat : ℕ) : ℤ) :=
            (Int.toNat_of_nonneg hfloor0).symm
          _ = ((Nat.floor t : ℕ) : ℤ) := by rw [Int.floor_toNat]
      exact_mod_cast hi
    have hiff (i : ℕ) :
        (((i + 1 : ℕ) : ℝ) - x) / (k : ℝ) ≤ alpha ↔ i < Nat.floor t := by
      rw [div_le_iff₀ hkpos]
      constructor
      · intro h
        have hreal : (((i + 1 : ℕ) : ℝ)) ≤ t := by
          dsimp [t]
          nlinarith
        exact Nat.lt_of_succ_le ((Nat.le_floor_iff ht0).mpr hreal)
      · intro h
        have hreal : (((i + 1 : ℕ) : ℝ)) ≤ t :=
          (Nat.le_floor_iff ht0).mp (Nat.succ_le_iff.mpr h)
        dsimp [t] at hreal
        nlinarith
    have hfilter : (range k).filter (fun i => i < Nat.floor t) = range (Nat.floor t) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    change (⌊t⌋ : ℝ) = _
    rw [hfloorNat]
    simp_rw [hiff]
    rw [Finset.sum_boole, hfilter, card_range]
  refine ⟨?_, hmass, ?_⟩
  · simpa only [F, hdrop] using hseries
  · calc
      geometricReadout r alpha x =
          ∑' j : ℕ, (1 - r) ^ 2 * r ^ j *
            (⌊x + ((j + 1 : ℕ) : ℝ) * alpha⌋ : ℝ) := by
              simpa only [F, hdrop] using hseries
      _ = _ := by
        apply tsum_congr
        intro j
        rw [hcount (j + 1) (Nat.succ_pos j)]

#print axioms geometric_readout_floor_series_and_mass

end D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries
