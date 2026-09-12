/- GID: D5/S1/Recurrence/LucasVerticalSlice
   generality: G
   mirror-B: D5/B/S1/Recurrence/LucasVerticalSlice
   mirror-E: none(waiver:formal-unit-only)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Recurrence/LucasVerticalSlice.claim; result=D5/S1/Recurrence/LucasVerticalSlice.result; claim=D5/S1/Recurrence/LucasVerticalSlice.claim
   digest: Trace, half-period, and unit-discriminant slice criteria, with a counterexample. -/

import D5.S1.Recurrence.LucasCompanion
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

/-!
A vertical slice exists exactly when two consecutive companion traces are minus two
and minus the first parameter. When four is nonzero, a vertical slice exists exactly
when these two traces occur at half the companion period. When the discriminant is
a unit, a vertical slice exists exactly when minus one is an integer companion power.
The unit-discriminant hypothesis in the third criterion is not removable, as `result`
proves by refuting `claim`. The non-removability of the nonzero-four hypothesis in the
second criterion is measured but not proved in this module.
-/

namespace D5.S1.Recurrence.LucasVerticalSlice

open Matrix LucasEvenDescent LucasCompanion

variable {R : Type*} [CommRing R]

private theorem power_shape (p : R) (q : Rˣ) (n : ℤ) :
    (↑(companion p q ^ n) : Matrix (Fin 2) (Fin 2) R) =
      !![lucasU p q (n + 1), -(q : R) * lucasU p q n;
         lucasU p q n, lucasU p q (n + 1) - p * lucasU p q n] :=
  companion_power_shape p q n

private theorem trace_power_mul (p : R) (q : Rˣ) (n : ℤ)
    (A : Matrix (Fin 2) (Fin 2) R) :
    Matrix.trace ((↑(companion p q ^ n) : Matrix (Fin 2) (Fin 2) R) * A) =
      lucasU p q n * Matrix.trace ((companion p q : Matrix (Fin 2) (Fin 2) R) * A) +
        (lucasU p q (n + 1) - p * lucasU p q n) * Matrix.trace A := by
  rw [power_shape]
  simp [companion, Matrix.trace_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

private theorem trace_addition (p : R) (q : Rˣ) (n s : ℤ) :
    lucasV p q (n + s) = lucasU p q n * lucasV p q (s + 1) +
      (lucasU p q (n + 1) - p * lucasU p q n) * lucasV p q s := by
  have hs : (companion p q : Matrix (Fin 2) (Fin 2) R) *
      (↑(companion p q ^ s) : Matrix (Fin 2) (Fin 2) R) =
        ↑(companion p q ^ (s + 1)) := by
    rw [add_comm s 1, zpow_add]
    simp
  unfold lucasV
  rw [zpow_add, Units.val_mul, trace_power_mul, hs]

/-- Two consecutive traces characterize a vertical slice over any commutative ring. -/
theorem verticalSlice_iff_two_traces (p : R) (q : Rˣ) :
    (∃ s : ℤ, ∀ n : ℤ, lucasV p q n + lucasV p q (n + s) = 0) ↔
      ∃ s : ℤ, lucasV p q s = -2 ∧ lucasV p q (s + 1) = -p := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_, ?_⟩
    · have h := hs 0
      rw [zero_add, (lucasV_recurrence p q).1] at h
      linear_combination h
    · have h := hs 1
      rw [(lucasV_recurrence p q).2.1, add_comm 1 s] at h
      linear_combination h
  · rintro ⟨s, h0, h1⟩
    refine ⟨s, fun n => ?_⟩
    rw [trace_addition, h0, h1, lucasV_eq_lucasU]
    ring

private theorem period_dvd_int (p : R) (q : Rˣ) (s : ℤ) :
    (companionPeriod p q : ℤ) ∣ s ↔ Function.Periodic (lucasV p q) s := by
  constructor
  · rintro ⟨k, hk⟩
    rw [hk, mul_comm]
    exact ((companionPeriod_dvd_iff p q _).mp (dvd_refl _)).int_mul k
  · intro hs
    have habs : Function.Periodic (lucasV p q) (s.natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      rcases le_total 0 s with h | h
      · simpa only [abs_of_nonneg h] using hs
      · simpa only [abs_of_nonpos h] using hs.neg
    exact Int.natCast_dvd.mpr ((companionPeriod_dvd_iff p q _).mpr habs)

/-- When four is nonzero, the half companion period witnesses every existing slice. -/
theorem verticalSlice_iff_half_companionPeriod (p : R) (q : Rˣ) (h4 : (4 : R) ≠ 0) :
    (∃ s : ℤ, ∀ n : ℤ, lucasV p q n + lucasV p q (n + s) = 0) ↔
      ∃ T : ℕ, companionPeriod p q = 2 * T ∧
        lucasV p q (T : ℤ) = -2 ∧ lucasV p q ((T : ℤ) + 1) = -p := by
  constructor
  · rintro ⟨s, hs⟩
    have ha : Function.Antiperiodic (lucasV p q) s := by
      intro n
      exact eq_neg_of_add_eq_zero_right (hs n)
    let P : ℤ := companionPeriod p q
    have hd : P ∣ 2 * s := (period_dvd_int p q _).mpr ha.periodic_two_mul
    have hn : ¬ P ∣ s := by
      intro h
      have hpos := ((period_dvd_int p q s).mp h).eq
      have hneg := ha.eq
      rw [(lucasV_recurrence p q).1] at hpos hneg
      apply h4
      linear_combination hneg - hpos
    have hP : 0 < P := by
      have hnonneg : 0 ≤ P := Int.natCast_nonneg _
      by_contra h
      have hz : P = 0 := by omega
      rw [hz, zero_dvd_iff] at hd hn
      omega
    let r : ℤ := s % P
    have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hP)
    have hrlt : r < P := Int.emod_lt_of_pos _ hP
    have hrne : r ≠ 0 := by
      intro h
      exact hn (Int.dvd_iff_emod_eq_zero.mpr h)
    have hrmod : (2 * r) % P = 0 := by
      change (2 * (s % P)) % P = 0
      rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
      exact Int.dvd_iff_emod_eq_zero.mp hd
    have hhalf : P = 2 * r := by
      by_cases hlt : 2 * r < P
      · rw [Int.emod_eq_of_lt (by omega) hlt] at hrmod
        omega
      · rw [Int.emod_eq_sub_self_emod,
          Int.emod_eq_of_lt (by omega : 0 ≤ 2 * r - P) (by omega)] at hrmod
        omega
    have hshift (n : ℤ) : lucasV p q (n + s) = lucasV p q (n + r) := by
      have hp : Function.Periodic (lucasV p q) P :=
        (companionPeriod_dvd_iff p q _).mp (dvd_refl _)
      have h := hp.int_mul (s / P) (n + r)
      have he : n + r + s / P * P = n + s := by
        dsimp [r]
        have he := Int.emod_add_ediv_mul s P
        linear_combination he
      simpa only [Int.cast_id, he] using h
    refine ⟨r.toNat, ?_, ?_, ?_⟩
    · have he : (companionPeriod p q : ℤ) = 2 * (r.toNat : ℤ) := by
        simpa only [Int.toNat_of_nonneg hr0] using hhalf
      exact_mod_cast he
    · rw [Int.toNat_of_nonneg hr0]
      have h := (hshift 0).symm.trans (ha 0)
      simpa only [zero_add, (lucasV_recurrence p q).1] using h
    · rw [Int.toNat_of_nonneg hr0]
      have h := (hshift 1).symm.trans (ha 1)
      simpa only [add_comm 1 r, (lucasV_recurrence p q).2.1] using h
  · rintro ⟨T, _, h0, h1⟩
    exact (verticalSlice_iff_two_traces p q).mpr ⟨(T : ℤ), h0, h1⟩

/-- A unit discriminant makes the trace criterion detect the scalar minus one. -/
theorem verticalSlice_iff_neg_one_mem_zpowers (p : R) (q : Rˣ)
    (hu : IsUnit ((p : R) ^ 2 - 4 * (q : R))) :
    (∃ s : ℤ, ∀ n : ℤ, lucasV p q n + lucasV p q (n + s) = 0) ↔
      ∃ s : ℤ, companion p q ^ s = -1 := by
  constructor
  · intro h
    obtain ⟨s, h0, h1⟩ := (verticalSlice_iff_two_traces p q).mp h
    let a := lucasU p q (s + 1) - p * lucasU p q s + 1
    let b := lucasU p q s
    have ht0 : 2 * a + p * b = 0 := by
      rw [lucasV_eq_lucasU] at h0
      dsimp [a, b]
      linear_combination h0
    have ht1 : p * a + (p ^ 2 - 2 * (q : R)) * b = 0 := by
      rw [lucasV_eq_lucasU,
        show s + 1 + 1 = s + 2 by omega, (lucas_recurrence p q).2.2] at h1
      dsimp [a, b]
      linear_combination h1
    have hb : b = 0 := by
      apply hu.mul_right_eq_zero.mp
      linear_combination 2 * ht1 - p * ht0
    have ha : a = 0 := by
      apply hu.mul_right_eq_zero.mp
      linear_combination (p ^ 2 - 2 * (q : R)) * ht0 - p * ht1
    have hs0 : lucasU p q s = 0 := hb
    have hs1 : lucasU p q (s + 1) = -1 := by
      dsimp [a] at ha
      rw [hs0] at ha
      linear_combination ha
    refine ⟨s, Units.ext ?_⟩
    rw [power_shape, hs0, hs1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rintro ⟨s, hs⟩
    refine ⟨s, fun n => ?_⟩
    simp [lucasV, zpow_add, hs, Matrix.trace_neg]

/-- The claim that the structural criterion needs no hypothesis. -/
def claim : Prop :=
  ∀ (m : ℕ) (p : ZMod m) (q : (ZMod m)ˣ),
    (∃ s : ℤ, ∀ n : ℤ, lucasV p q n + lucasV p q (n + s) = 0) ↔
      ∃ s : ℤ, companion p q ^ s = -1

private theorem witness_order : orderOf (companion (4 : ZMod 6) 1) = 6 := by
  apply (orderOf_eq_iff (by decide : 0 < 6)).mpr
  constructor
  · decide
  · intro k hk hk0
    interval_cases k <;> decide

private theorem witness_no_neg_one :
    ¬ ∃ s : ℤ, companion (4 : ZMod 6) 1 ^ s = -1 := by
  rintro ⟨s, hs⟩
  have hmod := zpow_mod_orderOf (companion (4 : ZMod 6) 1) s
  rw [witness_order] at hmod
  have hr : companion (4 : ZMod 6) 1 ^ (s % 6) = -1 := hmod.trans hs
  have hlo : 0 ≤ s % 6 := Int.emod_nonneg _ (by decide)
  have hhi : s % 6 < 6 := Int.emod_lt_of_pos _ (by decide)
  interval_cases s % 6 <;> revert hr <;> decide

/-- Modulo six, the trace slice exists but no integer companion power is minus one. -/
theorem result : ¬ claim := by
  intro h
  apply witness_no_neg_one
  apply (h 6 4 1).mp
  apply (verticalSlice_iff_two_traces (4 : ZMod 6) 1).mpr
  refine ⟨1, ?_, ?_⟩
  · rw [(lucasV_recurrence (4 : ZMod 6) 1).2.1]
    decide
  · have hrec := (lucasV_recurrence (4 : ZMod 6) 1).2.2 0
    norm_num only [zero_add, (lucasV_recurrence (4 : ZMod 6) 1).1,
      (lucasV_recurrence (4 : ZMod 6) 1).2.1, Units.val_one] at hrec
    norm_num only [Int.reduceAdd]
    rw [hrec]
    decide

-- Public declaration axiom audit.
#print axioms verticalSlice_iff_two_traces
#print axioms verticalSlice_iff_half_companionPeriod
#print axioms verticalSlice_iff_neg_one_mem_zpowers
#print axioms claim
#print axioms result

end D5.S1.Recurrence.LucasVerticalSlice
