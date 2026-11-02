/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S0.Certificates.JacoExponentialDominationRefutation]
   utility: none
   digest: The recursive Jaco endpoint array satisfies its all-order source recurrence. -/

import D5.S0.Certificates.JacoExponentialDominationRefutation
import Mathlib

/-! The recursive carrier, interval counting, and irrational Beatty inversion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty

open D5.S0.Certificates.JacoExponentialDominationRefutation

private theorem table_size (n : ℕ) : (endpointTable n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [endpointTable, extendEndpoints, ih]

private theorem table_entry (n i : ℕ) (hi : i ≤ n) :
    (endpointTable n)[i]! = jacoRight i := by
  induction n with
  | zero =>
      have : i = 0 := by omega
      subst i
      rfl
  | succ n ih =>
      by_cases h : i ≤ n
      · have hsize : i < (endpointTable n).size := by rw [table_size]; omega
        have hnew : i < (endpointTable (n + 1)).size := by rw [table_size]; omega
        have hprefix : (endpointTable (n + 1))[i]! = (endpointTable n)[i]! := by
          rw [getElem!_pos (endpointTable (n + 1)) i hnew,
            getElem!_pos (endpointTable n) i hsize]
          simp only [endpointTable, extendEndpoints]
          exact Array.getElem_push_lt hsize
        exact hprefix.trans (ih h)
      · have heq : i = n + 1 := by omega
        subst i
        simp [jacoRight, endpointTable, extendEndpoints, ← table_size n]

/-- The array carrier obeys the source recurrence at every positive index. -/
theorem endpoint_recurrence (n : ℕ) (hn : 1 ≤ n) :
    jacoRight n = 2 * n -
      ((Finset.range n).filter fun i => 1 ≤ i ∧ n ≤ jacoRight i).card := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hfilter :
      ((Finset.range (m + 1)).filter fun i =>
        1 ≤ i ∧ m + 1 ≤ (endpointTable m)[i]!) =
      ((Finset.range (m + 1)).filter fun i => 1 ≤ i ∧ m + 1 ≤ jacoRight i) := by
    apply Finset.filter_congr
    intro i hi
    rw [table_entry m i (by have := Finset.mem_range.mp hi; omega)]
  have hformula : jacoRight (m + 1) = 2 * (m + 1) -
      ((Finset.range (m + 1)).filter fun i =>
        1 ≤ i ∧ m + 1 ≤ (endpointTable m)[i]!).card := by
    simp [jacoRight, endpointTable, extendEndpoints]
  rw [hformula, hfilter]

/-- The golden Beatty candidate for the infinite outdegree. -/
noncomputable def beattyOut (n : ℕ) : ℕ := ⌊((n : ℝ) + 1) / Real.goldenRatio⌋₊

private theorem phi_split : Real.goldenRatio = 1 + 1 / Real.goldenRatio := by
  rw [one_div, Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

private theorem floor_endpoint (i : ℕ) :
    ⌊((i : ℝ) + 1) * Real.goldenRatio⌋₊ = i + 1 + beattyOut i := by
  have he : ((i : ℝ) + 1) * Real.goldenRatio =
      ((i : ℝ) + 1) / Real.goldenRatio + (i + 1 : ℕ) := by
    conv_lhs => rw [phi_split]
    push_cast
    ring
  rw [he, Nat.floor_add_natCast (by positivity)]
  dsimp [beattyOut]
  omega

theorem beatty_bounds (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ beattyOut n ∧ beattyOut n ≤ n := by
  have hp := Real.goldenRatio_pos
  have hp1 := Real.one_lt_goldenRatio
  have hp2 := Real.goldenRatio_lt_two
  constructor
  · apply (Nat.le_floor_iff (by positivity)).2
    rw [le_div_iff₀ hp]
    norm_num
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · have hlt : ((n : ℝ) + 1) / Real.goldenRatio < (n + 1 : ℕ) := by
      rw [div_lt_iff₀ hp]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have := (Nat.floor_lt (by positivity)).2 hlt
    exact Nat.le_of_lt_succ this

theorem beatty_threshold (n i : ℕ) :
    n ≤ i + beattyOut i ↔ beattyOut n ≤ i := by
  have hp := Real.goldenRatio_pos
  have hn0 : 0 ≤ ((n : ℝ) + 1) / Real.goldenRatio := by positivity
  have hi0 : 0 ≤ ((i : ℝ) + 1) * Real.goldenRatio := by positivity
  have hirr : ((n : ℝ) + 1) / Real.goldenRatio ≠ (i + 1 : ℕ) := by
    have h := (Real.goldenRatio_irrational.natCast_div
      (Nat.succ_ne_zero n)).ne_nat (i + 1)
    simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] using h
  calc
    n ≤ i + beattyOut i ↔ n + 1 ≤ ⌊((i : ℝ) + 1) * Real.goldenRatio⌋₊ := by
      rw [floor_endpoint]; omega
    _ ↔ (n + 1 : ℕ) ≤ ((i : ℝ) + 1) * Real.goldenRatio :=
      Nat.le_floor_iff hi0
    _ ↔ ((n : ℝ) + 1) / Real.goldenRatio ≤ (i + 1 : ℕ) := by
      rw [div_le_iff₀ hp]
      push_cast
      ring_nf
    _ ↔ ((n : ℝ) + 1) / Real.goldenRatio < (i + 1 : ℕ) :=
      ⟨fun h => lt_of_le_of_ne h hirr, le_of_lt⟩
    _ ↔ beattyOut n ≤ i := by
      rw [← Nat.floor_lt hn0]
      dsimp [beattyOut]
      omega

/-- The actual recursive endpoint is the all-order golden Beatty endpoint. -/
theorem endpoint_eq_beatty (n : ℕ) : jacoRight n = n + beattyOut n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        have hsmall : (1 : ℝ) / Real.goldenRatio < 1 :=
          (div_lt_one Real.goldenRatio_pos).2 Real.one_lt_goldenRatio
        simp only [beattyOut, Nat.cast_zero, zero_add]
        rw [Nat.floor_eq_zero.mpr hsmall]
        rfl
      · have hn1 : 1 ≤ n := by omega
        rw [endpoint_recurrence n hn1]
        have hbounds := beatty_bounds n hn1
        have hset : ((Finset.range n).filter fun i =>
            1 ≤ i ∧ n ≤ jacoRight i) = Finset.Ico (beattyOut n) n := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
          constructor
          · rintro ⟨hin, hi1, hreach⟩
            rw [ih i hin] at hreach
            exact ⟨(beatty_threshold n i).mp hreach, hin⟩
          · rintro ⟨hib, hin⟩
            refine ⟨hin, by omega, ?_⟩
            rw [ih i hin]
            exact (beatty_threshold n i).mpr hib
        rw [hset, Nat.card_Ico]
        omega

#print axioms endpoint_recurrence
#print axioms endpoint_eq_beatty

end D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
