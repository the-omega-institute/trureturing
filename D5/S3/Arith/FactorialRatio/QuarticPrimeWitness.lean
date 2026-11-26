/- GID: D5/S3/Arith/FactorialRatio/QuarticPrimeWitness
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/QuarticPrimeWitness
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.DiophantineApproximation.Basic]
   utility: none
   digest: Admissible prime witnesses for quadratic logarithmic compression. -/

module

public import D5.S3.Arith.FactorialRatio.CompactFactorialGcd
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Prime-dependent parameters for the compact factorial family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FactorialRatio.CompactFactorialGcd

open Finset
open D5.S3.Arith.FactorialRatio.RankOneLCMGcd (tailLCM)

private theorem int_interval_card_le {L U : ℝ} (h : L ≤ U) :
    ((Icc ⌈L⌉ ⌊U⌋).card : ℝ) ≤ U - L + 1 := by
  by_cases hI : ⌈L⌉ ≤ ⌊U⌋
  · have hc := Int.card_Icc_of_le ⌈L⌉ ⌊U⌋ (show ⌈L⌉ ≤ ⌊U⌋ + 1 by omega)
    have hc' : ((Icc ⌈L⌉ ⌊U⌋).card : ℝ) =
        (⌊U⌋ : ℝ) + 1 - (⌈L⌉ : ℝ) := by
      simpa only [Int.cast_natCast, Int.cast_add, Int.cast_one, Int.cast_sub] using
        congrArg (fun n : ℤ => (n : ℝ)) hc
    linarith [Int.floor_le U, Int.le_ceil L]
  · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hI), Finset.card_empty, Nat.cast_zero]
    linarith

private theorem approx_mul_lt {r q a b : ℕ}
    (happrox : |(r : ℝ) * b - (a : ℝ) * q| < q) : r * b < (a + 1) * q := by
  have h := (le_abs_self ((r : ℝ) * b - (a : ℝ) * q)).trans_lt happrox
  have ht : (r : ℝ) * b < ((a : ℝ) + 1) * q := by linarith
  exact_mod_cast ht

/-- Fold the final quotient period into the first. Each of the resulting
fibers injects into a closed interval of integers of the same length. -/
private theorem residue_count_le_of_approx {r q a b t : ℕ} (hq : 0 < q) (ha : 0 < a)
    (happrox : |(r : ℝ) * b - (a : ℝ) * q| < q) :
    (((range r).filter (fun k => (k * b) % q ≤ t)).card : ℝ) ≤
      (a : ℝ) + (r : ℝ) * (t + |(r : ℝ) * b - (a : ℝ) * q|) / q := by
  let h : ℝ := (r : ℝ) * b - (a : ℝ) * q
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  let hits := (range r).filter (fun k => (k * b) % q ≤ t)
  let j : ℕ → ℕ := fun k => k * b / q
  let bin : ℕ → ℕ := fun k => if j k = a then 0 else j k
  let fold : ℕ → ℤ := fun k => if j k = a then (k : ℤ) - (r : ℤ) else k
  let D : ℝ := (q : ℝ) * a
  have hD : 0 < D := mul_pos hqR haR
  let L : ℝ := -(r : ℝ) * max h 0
  let U : ℝ := (r : ℝ) * t - (r : ℝ) * min h 0
  have hwidth : U - L = (r : ℝ) * (t + |h|) := by
    by_cases hh : 0 ≤ h
    · simp only [U, L, min_eq_right hh, max_eq_left hh, abs_of_nonneg hh]
      ring
    · have hh' : h ≤ 0 := (lt_of_not_ge hh).le
      simp only [U, L, min_eq_left hh', max_eq_right hh', abs_of_nonpos hh']
      ring
  have hLU : L ≤ U := sub_nonneg.mp (by rw [hwidth]; positivity)
  have hmaps : (hits : Set ℕ).MapsTo bin (range a) := by
    intro k hk
    have hk' := Finset.mem_range.mp (Finset.mem_filter.mp (show k ∈ hits from hk)).1
    have hrb := approx_mul_lt happrox
    have hj : j k ≤ a := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hq).mpr
      ((Nat.mul_le_mul_right b hk'.le).trans_lt hrb))
    apply Finset.mem_range.mpr
    by_cases he : j k = a
    · simpa [bin, he] using ha
    · simpa [bin, he] using lt_of_le_of_ne hj he
  have hinj : (hits : Set ℕ).InjOn fold := by
    intro k hk l hl he
    have hk' := Finset.mem_range.mp (Finset.mem_filter.mp (show k ∈ hits from hk)).1
    have hl' := Finset.mem_range.mp (Finset.mem_filter.mp (show l ∈ hits from hl)).1
    by_cases hkf : j k = a <;> by_cases hlf : j l = a <;>
      simp only [fold, hkf, hlf, ite_true, ite_false] at he <;> omega
  have hinterval (k : ℕ) (hk : k ∈ hits) :
      (L + (r : ℝ) * q * bin k) / D ≤ (fold k : ℝ) ∧
      (fold k : ℝ) ≤ (U + (r : ℝ) * q * bin k) / D := by
    obtain ⟨hk', ht⟩ := Finset.mem_filter.mp hk
    have hkr : (k : ℝ) ≤ r := by exact_mod_cast (Finset.mem_range.mp hk').le
    have hv : ((k * b % q : ℕ) : ℝ) ≤ t := by exact_mod_cast ht
    have hdiv : (q : ℝ) * j k + ((k * b % q : ℕ) : ℝ) = (k : ℝ) * b := by
      dsimp [j]
      exact_mod_cast Nat.div_add_mod (k * b) q
    have hid :
        D * (fold k : ℝ) - (r : ℝ) * q * bin k =
          (r : ℝ) * ((k * b % q : ℕ) : ℝ) - (k : ℝ) * h := by
      have hbase : D * (k : ℝ) - (r : ℝ) * q * j k =
          (r : ℝ) * ((k * b % q : ℕ) : ℝ) - (k : ℝ) * h := by
        dsimp [D, h]
        linear_combination -(r : ℝ) * hdiv
      by_cases he : j k = a
      · rw [he] at hbase
        simp only [fold, bin, he, ite_true, Int.cast_sub, Int.cast_natCast, Nat.cast_zero,
          mul_zero, sub_zero]
        dsimp [D] at hbase ⊢
        linear_combination hbase
      · simpa [fold, bin, he] using hbase
    have hlo : (r : ℝ) * min h 0 ≤ (k : ℝ) * h := calc
      _ ≤ (k : ℝ) * min h 0 := mul_le_mul_of_nonpos_right hkr (min_le_right _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
    have hhi : (k : ℝ) * h ≤ (r : ℝ) * max h 0 := calc
      _ ≤ (k : ℝ) * max h 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hkr (le_max_right _ _)
    have hvt := mul_le_mul_of_nonneg_left hv (show (0 : ℝ) ≤ r by positivity)
    have hv0 : 0 ≤ (r : ℝ) * ((k * b % q : ℕ) : ℝ) := by positivity
    constructor
    · apply (div_le_iff₀ hD).mpr
      dsimp [L]
      linarith [hid]
    · apply (le_div_iff₀ hD).mpr
      dsimp [U]
      linarith [hid]
  have hfiber (i : ℕ) :
      ((hits.filter fun k => bin k = i).card : ℝ) ≤ (U - L) / D + 1 := by
    let left : ℝ := (L + (r : ℝ) * q * i) / D
    let right : ℝ := (U + (r : ℝ) * q * i) / D
    have hcard : (hits.filter fun k => bin k = i).card ≤ (Icc ⌈left⌉ ⌊right⌋).card := by
      apply Finset.card_le_card_of_injOn fold
      · intro k hk
        obtain ⟨hk', hi⟩ := Finset.mem_filter.mp (show k ∈ hits.filter _ from hk)
        obtain ⟨hl, hr⟩ := hinterval k hk'
        rw [hi] at hl hr
        exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr hl, Int.le_floor.mpr hr⟩
      · intro k hk l hl he
        exact hinj (Finset.mem_filter.mp (show k ∈ hits.filter _ from hk)).1
          (Finset.mem_filter.mp (show l ∈ hits.filter _ from hl)).1 he
    calc
      _ ≤ ((Icc ⌈left⌉ ⌊right⌋).card : ℝ) := by exact_mod_cast hcard
      _ ≤ right - left + 1 := int_interval_card_le
        (div_le_div_of_nonneg_right (add_le_add_left hLU _) hD.le)
      _ = _ := by dsimp [right, left]; rw [← sub_div]; ring
  change (hits.card : ℝ) ≤ (a : ℝ) + (r : ℝ) * (t + |h|) / q
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  calc
    _ ≤ ∑ _i ∈ range a, ((U - L) / D + 1) := Finset.sum_le_sum fun i _ => hfiber i
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hwidth]
      dsimp [D]
      field_simp [haR.ne', hqR.ne']; ring

/-- The selected parameter's single floor excess, before minimizing over the family. -/
private theorem selberg_floor_excess_le {r q a b s : ℕ} (hr : 1 ≤ r) (hq : 0 < q)
    (hqs : q ≤ s) (ha : 0 < a) (hb : r * b ≤ s) (hbq : b < q)
    (happrox : |(r : ℝ) * b - (a : ℝ) * q| < q) :
    (floorSum q r s b : ℝ) ≤
      (((r * s + (r - 1)) / q - (r - 1) : ℕ) : ℝ) +
        (2 * (a : ℝ) + (r : ℝ) * |(r : ℝ) * b - (a : ℝ) * q| / q) := by
  let B := (r * (s % q) + (r - 1)) / q
  have hres := residue_count_le_of_approx (t := s % q) hq ha happrox
  have ht := floorSum_telescoping hq hb
  rw [Nat.div_eq_of_lt hbq, Nat.mul_zero, Nat.add_zero] at ht
  have hh := compactTail_floor_add hq hqs hr
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdiv : r * b / q ≤ a := Nat.lt_succ_iff.mp
    ((Nat.div_lt_iff_lt_mul hq).mpr (approx_mul_lt happrox))
  have hdivR : ((r * b / q : ℕ) : ℝ) ≤ a := by exact_mod_cast hdiv
  have hB : (r : ℝ) * ((s % q : ℕ) : ℝ) / q ≤ (B : ℝ) + 1 := by
    have hmod := Nat.mod_lt (r * (s % q) + (r - 1)) hq
    have hdecomp := Nat.div_add_mod (r * (s % q) + (r - 1)) q
    have hnat : r * (s % q) ≤ (B + 1) * q := by
      change q * B + _ = _ at hdecomp
      rw [Nat.add_mul, Nat.one_mul, mul_comm B q]
      omega
    apply (div_le_iff₀ hqR).mpr
    exact_mod_cast hnat
  have htR := congrArg (fun n : ℕ => (n : ℝ)) ht
  have hhR := congrArg (fun n : ℕ => (n : ℝ)) hh
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at htR hhR
  change _ + (r : ℝ) = (r : ℝ) * ((s / q : ℕ) : ℝ) + (B : ℝ) + 1 at hhR
  rw [mul_add, add_div] at hres
  linarith only [htR, hhR, hres, hdivR, hB]

private theorem approximation {r q A : ℕ} (hr : 0 < r) (hrq : r < q) (hA : 0 < A) :
    ∃ a b : ℕ, 0 < a ∧ a ≤ A ∧ |(r : ℝ) * b - (a : ℝ) * q| ≤ r / ((A : ℝ) + 1) := by
  obtain ⟨j, k, hk, hkA, h⟩ :=
    Real.exists_int_int_abs_mul_sub_le ((q : ℝ) / r) hA
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrqR : (r : ℝ) < q := by exact_mod_cast hrq
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have heq : (r : ℝ) * (j : ℝ) - (k : ℝ) * q =
      (r : ℝ) * ((j : ℝ) - (k : ℝ) * ((q : ℝ) / r)) := by
    field_simp [hrR.ne']
  have hh : |(r : ℝ) * (j : ℝ) - (k : ℝ) * q| ≤ r / ((A : ℝ) + 1) := by
    rw [heq, abs_mul, abs_of_pos hrR, abs_sub_comm]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left h hrR.le
  have hj : 0 ≤ j := by
    have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
    have hqR : (0 : ℝ) ≤ q := by positivity
    have hkq := mul_le_mul_of_nonneg_right hkr hqR
    have hbudget : (r : ℝ) / ((A : ℝ) + 1) ≤ r :=
      div_le_self hrR.le (by linarith)
    have hlo := (abs_le.mp hh).1
    have : (0 : ℝ) ≤ (j : ℝ) := nonneg_of_mul_nonneg_right
      (by linarith only [hlo, hbudget, hkq, hrqR] :
        0 ≤ (r : ℝ) * (j : ℝ)) hrR
    exact_mod_cast this
  refine ⟨k.toNat, j.toNat, ?_, ?_, ?_⟩
  · exact_mod_cast (show (0 : ℤ) < (k.toNat : ℤ) by rwa [Int.toNat_of_nonneg hk.le])
  · exact_mod_cast (show (k.toNat : ℤ) ≤ (A : ℤ) by rwa [Int.toNat_of_nonneg hk.le])
  · have hkR : (k.toNat : ℝ) = (k : ℝ) := by
      rw [← Int.cast_natCast k.toNat, Int.toNat_of_nonneg hk.le]
    have hjR : (j.toNat : ℝ) = (j : ℝ) := by
      rw [← Int.cast_natCast j.toNat, Int.toNat_of_nonneg hj]
    rw [hkR, hjR]
    exact hh

private theorem quartic_size {r : ℕ} (hr : 8 ≤ r) :
    (r - 1) * (r - 2) = r * (r - 3) + 2 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = k + 3 := ⟨r - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    Nat.add_sub_cancel]
  ring

/-- The exact quartic factorial arguments are below the square of the number of parts. -/
public theorem quartic_size_lt_sq {r : ℕ} (hr : 8 ≤ r) :
    (r - 1) * (r - 2) < r ^ 2 := by
  rw [pow_two]
  exact Nat.mul_lt_mul_of_le_of_lt (Nat.sub_le r 1) (by omega) (by omega)

private theorem main_witness {r q : ℕ} (hr : 8 ≤ r) (hrq : r < q)
    (hq4 : q ≤ r ^ 2 / 4) :
    ∃ a b : ℕ, 0 < a ∧ r * b ≤ (r - 1) * (r - 2) ∧
      |(r : ℝ) * b - (a : ℝ) * q| < q ∧
      2 * (a : ℝ) + (r : ℝ) * |(r : ℝ) * b - (a : ℝ) * q| / q ≤
        3 * (r : ℝ) / Real.sqrt q := by
  let A := Nat.sqrt (r ^ 2 / q)
  have hq : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hr8 : (8 : ℝ) ≤ r := by exact_mod_cast hr
  have hrqR : (r : ℝ) < q := by exact_mod_cast hrq
  have h4 : q * 4 ≤ r ^ 2 := (Nat.le_div_iff_mul_le (by decide : 0 < (4 : ℕ))).mp hq4
  have hA2 : 2 ≤ A := by
    apply Nat.le_sqrt.mpr
    apply (Nat.le_div_iff_mul_le hq).mpr
    calc
      (2 : ℕ) * 2 * q = q * 4 := by ring
      _ ≤ r ^ 2 := h4
  have hA : 0 < A := (by decide : 0 < (2 : ℕ)).trans_le hA2
  obtain ⟨a, b, ha, haA, happ⟩ := approximation (by omega : 0 < r) hrq hA
  have hloN : A ^ 2 * q ≤ r ^ 2 :=
    (Nat.le_div_iff_mul_le hq).mp (Nat.sqrt_le' _)
  have hhiN : r ^ 2 < (A + 1) ^ 2 * q :=
    (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_sqrt' _)
  let z := Real.sqrt (q : ℝ)
  have hz : 0 < z := Real.sqrt_pos.2 hqR
  have hz2 : z ^ 2 = (q : ℝ) := Real.sq_sqrt hqR.le
  have hlo : ((A : ℝ) * z) ^ 2 ≤ (r : ℝ)^2 := by
    rw [mul_pow, hz2]
    exact_mod_cast hloN
  have hhi : (r : ℝ)^2 < (((A : ℝ) + 1) * z) ^ 2 := by
    rw [mul_pow, hz2]
    exact_mod_cast hhiN
  have hAz : (A : ℝ) * z ≤ r := by
    by_contra! hbad
    exact (not_lt_of_ge hlo) (sq_lt_sq' (by linarith) hbad)
  have hrAz : (r : ℝ) < ((A : ℝ) + 1) * z := by
    by_contra! hbad
    exact (not_le_of_gt hhi) (pow_le_pow_left₀ (by positivity) hbad 2)
  have hzhalf : z ≤ (r : ℝ) / 2 := by
    have h4R : (q : ℝ) * 4 ≤ (r : ℝ)^2 := by exact_mod_cast h4
    by_contra! hbad
    have hh := sq_lt_sq' (show -z < (r : ℝ) / 2 by linarith) hbad
    nlinarith only [hh, h4R, hz2]
  have hA1 : (1 : ℝ) ≤ (A : ℝ) + 1 := by
    linarith only [show (0 : ℝ) ≤ A by positivity]
  have hbudget : (r : ℝ) / ((A : ℝ) + 1) ≤ r := div_le_self hrR.le hA1
  have hqA : (A : ℝ) * q ≤ (r : ℝ) * z := by
    have hh := mul_le_mul_of_nonneg_right hAz hz.le
    rw [mul_assoc, ← pow_two, hz2] at hh
    exact hh
  have haAR : (a : ℝ) ≤ A := by exact_mod_cast haA
  have haq : (a : ℝ) * q ≤ (A : ℝ) * q := mul_le_mul_of_nonneg_right haAR hqR.le
  have hbz : (b : ℝ) ≤ z + 1 := by
    have hh := (abs_le.mp happ).2.trans hbudget
    apply (le_of_mul_le_mul_left ?_ hrR)
    linarith only [hh, haq, hqA, show (r : ℝ) * (z + 1) = r * z + r by ring]
  have hbN : b ≤ r - 3 := by
    have h : (b : ℝ) + 3 ≤ r := by linarith only [hbz, hzhalf, hr8]
    have h' : b + 3 ≤ r := by exact_mod_cast h
    omega
  refine ⟨a, b, ha, ?_, (happ.trans hbudget).trans_lt hrqR, ?_⟩
  · rw [quartic_size hr]
    exact (Nat.mul_le_mul_left _ hbN).trans (Nat.le_add_right _ _)
  · have haZ : (a : ℝ) ≤ (r : ℝ) / z := (le_div_iff₀ hz).mpr
      ((mul_le_mul_of_nonneg_right haAR hz.le).trans hAz)
    have hbudgetZ : (r : ℝ) / ((A : ℝ) + 1) ≤ z :=
      (div_le_iff₀ (by positivity)).mpr (by linarith only [hrAz])
    have hdisplacement : (r : ℝ) * |(r : ℝ) * b - (a : ℝ) * q| / q ≤ r / z := calc
      _ ≤ (r : ℝ) * z / q := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (happ.trans hbudgetZ) hrR.le) hqR.le
      _ = _ := by rw [← hz2]; field_simp [hz.ne'] <;> ring
    change _ ≤ 3 * (r : ℝ) / z
    rw [mul_div_assoc (3 : ℝ) (r : ℝ) z]
    linarith only [haZ, hdisplacement]

private theorem floor_witness {r q s : ℕ} (hr : 0 < r) (hrq : r < q)
    (hqs : q ≤ s) (hs : s < r ^ 2) (hq4 : r ^ 2 / 4 < q) :
    r * (q / r) ≤ s ∧ |(r : ℝ) * ((q / r : ℕ) : ℝ) - q| < q ∧
      2 + (r : ℝ) * |(r : ℝ) * ((q / r : ℕ) : ℝ) - q| / q ≤
        4 * (r : ℝ) / Real.sqrt q := by
  have hrem := Nat.div_add_mod q r
  have hlt := Nat.mod_lt q hr
  have hq : 0 < q := hr.trans hrq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrqR : (r : ℝ) < q := by exact_mod_cast hrq
  have hremR : (r : ℝ) * ((q / r : ℕ) : ℝ) + ((q % r : ℕ) : ℝ) = q := by
    exact_mod_cast hrem
  have habs : |(r : ℝ) * ((q / r : ℕ) : ℝ) - q| = ((q % r : ℕ) : ℝ) := by
    have he : (r : ℝ) * ((q / r : ℕ) : ℝ) - q = -((q % r : ℕ) : ℝ) := by linarith
    rw [he, abs_neg, abs_of_nonneg (by positivity)]
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hv : ((q % r : ℕ) : ℝ) < r := by exact_mod_cast hlt
  have happrox : |(r : ℝ) * ((q / r : ℕ) : ℝ) - q| < q := by
    rw [habs]
    exact hv.trans hrqR
  refine ⟨by omega, happrox, ?_⟩
  let z := Real.sqrt (q : ℝ)
  have hz : 0 < z := Real.sqrt_pos.2 hqR
  have hz2 : z ^ 2 = (q : ℝ) := Real.sq_sqrt hqR.le
  have hlo : z ≤ (r : ℝ) := by
    have h : (q : ℝ) ≤ (r : ℝ)^2 := by exact_mod_cast hqs.trans hs.le
    by_contra! hbad
    exact (not_lt_of_ge (hz2.trans_le h)) (sq_lt_sq' (by linarith) hbad)
  have hhi : (r : ℝ) ≤ 2 * z := by
    have h4 := (Nat.div_lt_iff_lt_mul (by decide : 0 < (4 : ℕ))).mp hq4
    have h4R : (r : ℝ)^2 < (q : ℝ) * 4 := by exact_mod_cast h4
    by_contra! hbad
    have hh := sq_lt_sq' (show -(r : ℝ) < 2 * z by linarith) hbad
    nlinarith only [hh, h4R, hz2]
  have h1 : 1 ≤ (r : ℝ) / z := (le_div_iff₀ hz).mpr (by simpa using hlo)
  have h2 : (r : ℝ) / z ≤ 2 := (div_le_iff₀ hz).mpr hhi
  have hcorr : (r : ℝ) * ((q % r : ℕ) : ℝ) / q ≤ ((r : ℝ) / z)^2 := calc
    _ ≤ (r : ℝ) * r / q := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hv.le hrR.le) hqR.le
    _ = _ := by rw [div_pow, hz2, pow_two (r : ℝ)]
  have hsq := mul_le_mul_of_nonneg_right h2 (show 0 ≤ (r : ℝ) / z by positivity)
  rw [habs, mul_div_assoc (4 : ℝ) (r : ℝ) (Real.sqrt q)]
  change _ ≤ 4 * ((r : ℝ) / z)
  nlinarith only [h1, hsq, hcorr]

/-- The stronger bound is attained by one explicit parameter for each large
base, before any use of primality or of the gcd. -/
private theorem quartic_large_base_witness {r q : ℕ} (hr : 8 ≤ r) (hrq : r < q)
    (hqs : q ≤ (r - 1) * (r - 2)) :
    ∃ b : ℕ, r * b ≤ (r - 1) * (r - 2) ∧
      (floorSum q r ((r - 1) * (r - 2)) b : ℝ) ≤
        (((r * ((r - 1) * (r - 2)) + (r - 1)) / q - (r - 1) : ℕ) : ℝ) +
          4 * (r : ℝ) / Real.sqrt q := by
  let s := (r - 1) * (r - 2)
  have hs : s < r ^ 2 := quartic_size_lt_sq hr
  have hq : 0 < q := by omega
  suffices hw : ∃ a b : ℕ, 0 < a ∧ r * b ≤ s ∧
      |(r : ℝ) * b - (a : ℝ) * q| < q ∧
      2 * (a : ℝ) + (r : ℝ) * |(r : ℝ) * b - (a : ℝ) * q| / q ≤
        4 * (r : ℝ) / Real.sqrt q by
    obtain ⟨a, b, ha, hb, happ, hbound⟩ := hw
    have hbr : b < r := by
      by_contra! h
      have hmul := Nat.mul_le_mul_left r h
      rw [← pow_two] at hmul
      exact (not_le_of_gt hs) (hmul.trans hb)
    exact ⟨b, hb, (selberg_floor_excess_le (by omega) hq hqs ha hb
      (hbr.trans hrq) happ).trans (add_le_add_right hbound _)⟩
  by_cases hq4 : q ≤ r ^ 2 / 4
  · obtain ⟨a, b, ha, hb, happ, hbound⟩ := main_witness hr hrq hq4
    have hstep : 3 * (r : ℝ) / Real.sqrt q ≤ 4 * (r : ℝ) / Real.sqrt q := by
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      linarith only [show (0 : ℝ) ≤ r by positivity]
    exact ⟨a, b, ha, hb, happ, hbound.trans hstep⟩
  · obtain ⟨hb, happ, hbound⟩ := floor_witness (by omega : 0 < r) hrq hqs hs (by omega)
    exact ⟨1, q / r, by decide, hb, by simpa using happ, by simpa using hbound⟩

public theorem log_le_three {p r s : ℕ} (hp : p.Prime) (hpr : p ≤ r)
    (hs0 : s ≠ 0) (hs : s < r ^ 2) : Nat.log p s ≤ 3 * Nat.log p r := by
  have hr0 := (hp.pos.trans_le hpr).ne'
  let J := Nat.log p r
  have hJ : 1 ≤ J := (Nat.le_log_iff_pow_le hp.one_lt hr0).mpr (by simpa using hpr)
  have hrp : r < p ^ (J + 1) := Nat.lt_pow_succ_log_self hp.one_lt r
  have hsP : s < p ^ (2 * (J + 1)) := calc
    _ < r ^ 2 := hs
    _ ≤ (p ^ (J + 1)) ^ 2 := Nat.pow_le_pow_left hrp.le 2
    _ = _ := by rw [← pow_mul, mul_comm (J + 1) 2]
  have h := (Nat.log_lt_iff_lt_pow hp.one_lt hs0).mpr hsP
  change Nat.log p s < 2 * (J + 1) at h
  omega

/-- Each prime has an admissible family member with the stated exponent budget.
The lower bound holds for every member by the separate paired-floor theorem. -/
public theorem quartic_prime_witness {r p : ℕ} (hr : 8 ≤ r) (hp : p.Prime) :
    let s := (r - 1) * (r - 2)
    let T := tailLCM (r * s + (r - 1)) (r - 1)
    (p ≤ r → r * 0 ≤ s ∧
      (selbergFactorial r s 0).factorization p ≤ T.factorization p + 3 * (r - 1) * Nat.log p r) ∧
    (r < p → p ≤ s → ∃ b : ℕ, r * b ≤ s ∧
      ((selbergFactorial r s b).factorization p : ℝ) ≤
        (T.factorization p : ℝ) + 4 * (r : ℝ) / Real.sqrt p) ∧
    (s < p → r * 0 ≤ s ∧ (selbergFactorial r s 0).factorization p = 0) := by
  dsimp only
  let s := (r - 1) * (r - 2)
  have hs0 : s ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hs : s < r ^ 2 := quartic_size_lt_sq hr
  have hr1 : 1 ≤ r := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro hpr
    refine ⟨by simp, (selberg_zero_factorization_le_log hp hr1).trans ?_⟩
    have h := Nat.mul_le_mul_right (r - 1) (log_le_three hp hpr hs0 hs)
    exact Nat.add_le_add_left (by simpa only [mul_assoc, mul_left_comm, mul_comm] using h) _
  · intro hrp hps
    obtain ⟨b, hb, hbound⟩ := quartic_large_base_witness hr hrp hps
    have hspp : s < p ^ 2 := hs.trans_le (Nat.pow_le_pow_left hrp.le 2)
    have hlog := (Nat.log_lt_iff_lt_pow hp.one_lt hs0).mpr hspp
    refine ⟨b, hb, ?_⟩
    rw [selberg_factorization hp hb hlog, compact_tail_factorization hp hr1 hspp]
    simpa only [Nat.Ico_succ_singleton 1, Finset.sum_singleton, pow_one] using hbound
  · intro hsp
    refine ⟨by simp, ?_⟩
    have hlog : Nat.log p s < 1 := by
      rw [Nat.log_of_lt (show s < p from hsp)]
      decide
    rw [selberg_factorization hp (by simp : r * 0 ≤ s) hlog, Finset.Ico_self, Finset.sum_empty]

end D5.S3.Arith.FactorialRatio.CompactFactorialGcd
