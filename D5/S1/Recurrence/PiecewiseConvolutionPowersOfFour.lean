/- GID: D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour
   generality: I
   mirror-B: D5/B/S1/Recurrence/PiecewiseConvolutionPowersOfFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The piecewise square and fourth-power convolution is odd at base-four repunits. -/

import D5.S1.Recurrence.ConvolutionRecurrenceOddPowersOfTwo
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.FieldTheory.Finite.Basic

open Finset PowerSeries
open D5.S1.Recurrence.ConvolutionRecurrenceOddPowersOfTwo (convolution_pairing)

namespace D5.S1.Recurrence.PiecewiseConvolutionPowersOfFour

private theorem pow_coeff_congr {R : Type*} [Semiring R] {f g : PowerSeries R}
    (n p : ℕ) (h : ∀ i ≤ n, coeff i f = coeff i g) : coeff n (f^p) = coeff n (g^p) := by
  induction p generalizing n with
  | zero => rfl
  | succ p ih =>
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    apply sum_congr rfl
    intro x hx
    have hb := Finset.mem_antidiagonal.mp hx
    rw [ih x.1 (fun i hi => h i (by omega)), h x.2 (by omega)]

noncomputable def seq (n : ℕ) : ℕ :=
  Nat.lt_wfRel.wf.fix (fun n rec => if n = 0 then 1 else
    coeff (n-1) ((mk (fun i => if hi : i < n then rec i hi else 0) : PowerSeries ℕ) ^
      (if Even n then 2 else 4))) n

private theorem seq_eq (n : ℕ) : seq n = if n=0 then 1 else
    coeff (n-1) ((mk (fun i => if i < n then seq i else 0) : PowerSeries ℕ) ^
      (if Even n then 2 else 4)) := by
  exact Nat.lt_wfRel.wf.fix_eq _ n

noncomputable def series : PowerSeries ℕ := mk seq

theorem seq_zero : seq 0 = 1 := by rw [seq_eq]; simp

theorem seq_recurrence {n : ℕ} (hn : 0 < n) :
    seq n = coeff (n-1) (series ^ (if Even n then 2 else 4)) := by
  rw [seq_eq, if_neg (by omega)]
  apply pow_coeff_congr
  intro i hi
  simp only [series, coeff_mk, if_pos (by omega : i < n)]

private theorem square_even_coeff (f : PowerSeries (ZMod 2))
    (hf : coeff 0 f = 0) {m : ℕ} (hm : 1 ≤ m) :
    coeff (2*m) (f^2) = coeff m f ^ 2 := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ]
  rw [sum_range_eq_add_Ico (fun k => coeff k f * coeff (2*m-k) f)
    (by omega : 0 < 2*m)]
  simp only [hf, zero_mul, Nat.sub_self, mul_zero, zero_add, add_zero]
  have he : Ico 1 (2*m) = Icc 1 (2*m-1) := by ext k; simp; omega
  rw [he]
  exact convolution_pairing (fun k => coeff k f) hm

private theorem square_odd_coeff (f : PowerSeries (ZMod 2)) (j : ℕ) :
    coeff (2*j+1) (f^2) = 0 := by
  let g : PowerSeries (ZMod 2) := X * f.expand 2 (by decide)
  have hg0 : coeff 0 g = 0 := by simp [g, coeff_zero_eq_constantCoeff]
  have hgmid : coeff (2*(j+1)) g = 0 := by
    dsimp [g]
    rw [← pow_one (X : PowerSeries (ZMod 2)), coeff_X_pow_mul', if_pos (by omega)]
    apply coeff_expand_of_not_dvd
    omega
  have h := square_even_coeff g hg0 (m := 2*(j+1)) (by omega)
  rw [hgmid, zero_pow (by decide : 2 ≠ 0)] at h
  have he : g^2 = X^2 * (f^2).expand 2 (by decide) := by
    dsimp [g]
    rw [mul_pow, map_pow]
  rw [he, coeff_X_pow_mul', if_pos (by omega),
    show 2*(2*(j+1))-2 = 2*(2*j+1) by omega, coeff_expand_mul] at h
  exact h

private noncomputable def binary : PowerSeries (ZMod 2) :=
  series.map (Nat.castRingHom (ZMod 2))

private theorem binary_coeff (n : ℕ) : coeff n binary = (seq n : ZMod 2) := by
  simp [binary, series, coeff_map]

private theorem binary_recurrence {n : ℕ} (hn : 0 < n) :
    (seq n : ZMod 2) = coeff (n-1) (binary ^ (if Even n then 2 else 4)) := by
  have h := congrArg (Nat.castRingHom (ZMod 2)) (seq_recurrence hn)
  rw [binary, ← map_pow, coeff_map]
  exact h

/-- Every positive even index has an even sequence value. -/
theorem seq_even_index_zero (j : ℕ) : (seq (2*j+2) : ZMod 2) = 0 := by
  rw [binary_recurrence (by omega), if_pos (show Even (2*j+2) from ⟨j+1, by omega⟩),
    show 2*j+2-1 = 2*j+1 by omega]
  exact square_odd_coeff binary j

private theorem square_expand (f : PowerSeries (ZMod 2)) : f.expand 2 (by decide) = f^2 := by
  have h := MvPowerSeries.map_frobenius_expand 2 (by decide : 2 ≠ 0) (f := f)
  change (f.expand 2 (by decide)).map (frobenius (ZMod 2) 2) = f ^ 2 at h
  rw [ZMod.frobenius_zmod, PowerSeries.map_id] at h
  exact h

private theorem fourth_expand (f : PowerSeries (ZMod 2)) : f.expand 4 (by decide) = f^4 := by
  calc
    f.expand 4 (by decide) = (f.expand 2 (by decide)).expand 2 (by decide) :=
      expand_mul 2 (by decide) 2 (by decide) f
    _ = f^4 := by rw [square_expand, square_expand, ← pow_mul]

private theorem fourth_coeff_three (f : PowerSeries (ZMod 2)) (j : ℕ) :
    coeff (4*j+2) (f^4) = 0 := by
  rw [← fourth_expand]
  apply coeff_expand_of_not_dvd
  omega

/-- The sequence vanishes modulo two at indices congruent to three modulo four. -/
theorem seq_four_mul_add_three (j : ℕ) : (seq (4*j+3) : ZMod 2) = 0 := by
  rw [binary_recurrence (by omega), if_neg (by
    rintro ⟨k, hk⟩
    omega), show 4*j+3-1 = 4*j+2 by omega]
  exact fourth_coeff_three binary j

/-- At indices congruent to one modulo four, parity descends to the quotient. -/
theorem seq_four_mul_add_one (j : ℕ) : (seq (4*j+1) : ZMod 2) = (seq j : ZMod 2) := by
  rw [binary_recurrence (by omega), if_neg (by
    rintro ⟨k, hk⟩
    omega), show 4*j+1-1 = 4*j by omega, ← fourth_expand, coeff_expand_mul, binary_coeff]

/-- The parity conjecture for OEIS A368628, including its index-zero initial value. -/
theorem a368628_odd_iff (n : ℕ) : Odd (seq n) ↔ ∃ k : ℕ, 3 * n + 1 = 4 ^ k := by
  rw [← ZMod.natCast_eq_one_iff_odd]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp only [seq_zero, Nat.cast_one, mul_zero, zero_add]
      exact iff_of_true trivial ⟨0, rfl⟩
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' n
    · have hn : n = 2*(j-1)+2 := by omega
      have hz : (seq n : ZMod 2) = 0 := hn ▸ seq_even_index_zero (j-1)
      rw [hz]
      apply iff_of_false zero_ne_one
      rintro ⟨k, hk⟩
      cases k with
      | zero => simp only [pow_zero] at hk; omega
      | succ k => rw [pow_succ] at hk; omega
    · obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' j
      · have hn : n = 4*m+1 := by omega
        have hc : (seq n : ZMod 2) = (seq m : ZMod 2) := hn ▸ seq_four_mul_add_one m
        rw [hc, ih m (by omega)]
        constructor
        · rintro ⟨k, hk⟩
          refine ⟨k+1, ?_⟩
          rw [pow_succ]
          omega
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp only [pow_zero] at hk; omega
          | succ k =>
            refine ⟨k, ?_⟩
            rw [pow_succ] at hk
            omega
      · have hn : n = 4*m+3 := by omega
        have hz : (seq n : ZMod 2) = 0 := hn ▸ seq_four_mul_add_three m
        rw [hz]
        apply iff_of_false zero_ne_one
        rintro ⟨k, hk⟩
        cases k with
        | zero => simp only [pow_zero] at hk; omega
        | succ k => rw [pow_succ] at hk; omega

#print axioms seq_zero
#print axioms seq_recurrence
#print axioms seq_even_index_zero
#print axioms seq_four_mul_add_three
#print axioms seq_four_mul_add_one
#print axioms a368628_odd_iff

-- A coefficient-level echo of the original integer recurrence, not of the parity theorem.
private theorem initial_echo : seq 0 = 1 ∧ seq 1 = 1 ∧ seq 2 = 2 ∧ seq 3 = 14 := by
  have h1 : seq 1 = 1 := by
    rw [seq_recurrence (by decide), if_neg (by decide : ¬Even 1)]
    norm_num only [Nat.sub_self, coeff_zero_eq_constantCoeff, map_pow]
    simp only [← coeff_zero_eq_constantCoeff, series, coeff_mk, seq_zero, one_pow]
  have h2 : seq 2 = 2 := by
    have h := seq_recurrence (n := 2) (by decide)
    norm_num [series, pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ, seq_zero, h1] at h
    exact h
  have h3 : seq 3 = 14 := by
    have h := seq_recurrence (n := 3) (by decide)
    rw [if_neg (by decide : ¬Even 3)] at h
    norm_num [series, pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ, seq_zero, h1, h2] at h
    exact h
  exact ⟨seq_zero, h1, h2, h3⟩

run_cmd do
  for (consumer, provider) in
      [( ``a368628_odd_iff, ``seq_even_index_zero),
       ( ``a368628_odd_iff, ``seq_four_mul_add_three),
       ( ``a368628_odd_iff, ``seq_four_mul_add_one),
       ( ``seq_even_index_zero, ``square_odd_coeff),
       ( ``square_odd_coeff, ``square_even_coeff),
       ( ``square_even_coeff, ``convolution_pairing),
       ( ``seq_recurrence, ``pow_coeff_congr)] do
    let some info := (← Lean.getEnv).checked.get.find? consumer
      | throwError "Missing declaration: {consumer}"
    let some value := info.value? (allowOpaque := true)
      | throwError "Missing proof body: {consumer}"
    unless value.getUsedConstants.contains provider do
      throwError "Missing elaborated dependency: {consumer} -> {provider}"
    Lean.logInfo m!"ELABORATED_DEPENDENCY {consumer} -> {provider}"

end D5.S1.Recurrence.PiecewiseConvolutionPowersOfFour
