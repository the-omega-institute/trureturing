/- GID: D5/S1/Words/Mechanical/MechanicalPeriodicity
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalPeriodicity
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: A lower mechanical word is eventually periodic exactly when its slope is rational. -/

import D5.S1.Words.Mechanical.MechanicalDensity
import Mathlib.Data.Nat.Periodic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S1.Words.Mechanical

/-- A lower mechanical word repeats with some positive period after a finite prefix. -/
def lowerMechanicalEventuallyPeriodic (alpha rho : Real) : Prop :=
  ∃ s p : Nat, 0 < p ∧ ∀ n,
    lowerMechanicalWord alpha rho (s + n + p) = lowerMechanicalWord alpha rho (s + n)

private theorem lower_mechanical_letter_rat_periodic (r : Rat) (rho : Real) :
    Function.Periodic (lowerMechanicalLetter (r : Real) rho) r.den := by
  have hshift (m : Nat) :
      rho + ((m + r.den : Nat) : Real) * (r : Real) =
        (r.num : Real) + (rho + (m : Real) * (r : Real)) := by
    rw [Rat.cast_def]
    push_cast
    field_simp [Rat.den_nz]
    ring
  intro n
  simp only [lowerMechanicalLetter]
  rw [show n + r.den + 1 = (n + 1) + r.den by omega, hshift (n + 1), hshift n]
  simp only [Int.floor_intCast_add]
  omega

/-- A rational slope gives a period equal to its reduced denominator, starting at zero. -/
theorem lower_mechanical_word_rat_periodic (r : Rat) (rho : Real) :
    Function.Periodic (lowerMechanicalWord (r : Real) rho) r.den := by
  intro n
  rw [Bool.eq_iff_iff, lowerMechanicalWord_eq_true_iff, lowerMechanicalWord_eq_true_iff]
  rw [lower_mechanical_letter_rat_periodic r rho n]

private theorem count_periodic_blocks (P : Nat → Prop) [DecidablePred P]
    {p : Nat} (hP : Function.Periodic P p) (k : Nat) :
    Nat.count P (k * p) = k * Nat.count P p := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, Nat.count_add, ih]
      have hcountshift :
          Nat.count (fun n => P (k * p + n)) p = Nat.count P p := by
        rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
        congr 1
        ext n
        simp only [Finset.mem_filter, Finset.mem_range]
        have hpoint : P (k * p + n) = P n := by
          simpa [Nat.add_comm] using hP.nat_mul k n
        constructor
        · rintro ⟨hn, hPn⟩
          exact ⟨hn, Eq.mp hpoint hPn⟩
        · rintro ⟨hn, hPn⟩
          exact ⟨hn, Eq.mpr hpoint hPn⟩
      rw [hcountshift]
      rw [Nat.succ_mul]

private theorem lower_mechanical_eventually_periodic_not_irrational {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hperiodic : lowerMechanicalEventuallyPeriodic alpha rho) : ¬ Irrational alpha := by
  rcases hperiodic with ⟨s, p, hp, hperiodic⟩
  let P : Nat → Prop := fun n => lowerMechanicalWord alpha rho (s + n) = true
  have hP : Function.Periodic P p := by
    intro n
    exact congrArg (· = true) (by simpa [P, Nat.add_assoc] using hperiodic n)
  let c : Nat := Nat.count P p
  have hwindow (n : Nat) :
      lowerMechanicalWindowTrueCount alpha rho s n = Nat.count P n := by
    rw [lowerMechanicalWindowTrueCount, Nat.count_eq_card_filter_range]
  have hblocks (k : Nat) :
      lowerMechanicalWindowTrueCount alpha rho s (k * p) = k * c := by
    rw [hwindow, count_periodic_blocks P hP]
  have hcount : (c : Real) = (p : Real) * alpha := by
    by_contra hne
    have hdelta_ne : (c : Real) - (p : Real) * alpha ≠ 0 := sub_ne_zero.mpr hne
    have hdelta : 0 < |(c : Real) - (p : Real) * alpha| := abs_pos.mpr hdelta_ne
    rcases exists_nat_one_div_lt hdelta with ⟨k, hk⟩
    let K : Nat := k + 1
    have hKpos : (0 : Real) < K := by
      exact_mod_cast Nat.succ_pos k
    have hlarge :
        1 < (K : Real) * |(c : Real) - (p : Real) * alpha| := by
      have hk' : 1 / (K : Real) < |(c : Real) - (p : Real) * alpha| := by
        simpa [K] using hk
      simpa [mul_comm] using (div_lt_iff₀ hKpos).mp hk'
    have hdisc := lower_mechanical_window_true_discrepancy
      (alpha := alpha) (rho := rho) halpha0 halpha1 s (K * p)
    rw [hblocks] at hdisc
    have hsmall :
        (K : Real) * |(c : Real) - (p : Real) * alpha| < 1 := by
      rw [← abs_of_pos hKpos, ← abs_mul]
      convert hdisc using 1
      push_cast
      ring
    linarith
  have hp_real : (p : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have halpha : alpha = (c : Real) / (p : Real) := by
    apply (eq_div_iff hp_real).2
    linarith
  intro hirrational
  apply hirrational
  refine ⟨(c : Rat) / (p : Rat), ?_⟩
  rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
  exact halpha.symm

/-- A lower mechanical word of slope in `[0, 1)` is eventually periodic iff the slope is rational. -/
theorem lower_mechanical_eventually_periodic_iff_not_irrational {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) :
    ¬ Irrational alpha ↔ lowerMechanicalEventuallyPeriodic alpha rho := by
  constructor
  · intro hnotirrational
    rcases exists_rat_of_not_irrational hnotirrational with ⟨r, rfl⟩
    refine ⟨0, r.den, r.den_pos, ?_⟩
    intro n
    simpa using lower_mechanical_word_rat_periodic r rho n
  · exact lower_mechanical_eventually_periodic_not_irrational halpha0 halpha1

private theorem one_third_lower_mechanical_periodic :
    Function.Periodic (lowerMechanicalWord (1 / 3 : Real) 0) 3 := by
  simpa using lower_mechanical_word_rat_periodic (1 / 3 : Rat) 0

private theorem one_third_lower_mechanical_first_period :
    List.ofFn (fun i : Fin 3 => lowerMechanicalWord (1 / 3 : Real) 0 i) =
      [false, false, true] := by
  norm_num [lowerMechanicalWord, lowerMechanicalLetter]

private theorem golden_slope_not_lower_mechanical_eventually_periodic :
    ¬ lowerMechanicalEventuallyPeriodic (Real.goldenRatio)⁻¹ 0 := by
  intro hperiodic
  have hnotirrational := lower_mechanical_eventually_periodic_iff_not_irrational
    (alpha := (Real.goldenRatio)⁻¹) (rho := 0)
    (inv_nonneg.mpr Real.goldenRatio_pos.le)
    (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio) |>.mpr hperiodic
  exact hnotirrational Real.goldenRatio_irrational.inv

#print axioms lower_mechanical_word_rat_periodic
#print axioms lower_mechanical_eventually_periodic_iff_not_irrational

end D5.S1.Words.Mechanical
