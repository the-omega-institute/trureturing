/- GID: D5/S1/Words/Mechanical/MechanicalDensity
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalDensity
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: General lower mechanical window discrepancy and fixed-start density. -/

import D5.S1.Words.Mechanical.MechanicalBalance

namespace D5.S1.Words.Mechanical

/- Every lower-mechanical window has true-count discrepancy strictly below one. -/
theorem lower_mechanical_window_true_discrepancy {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) (i n : Nat) :
    |(lowerMechanicalWindowTrueCount alpha rho i n : Real) - (n : Real) * alpha| < 1 := by
  let x : Real := rho + (i : Real) * alpha
  let t : Real := (n : Real) * alpha
  have hendpoint :
      rho + ((i + n : Nat) : Real) * alpha = x + t := by
    dsimp [x, t]
    push_cast
    ring
  have hcount_int := lowerMechanicalWindowTrueCount_eq_floor
    (alpha := alpha) (rho := rho) halpha0 halpha1 i n
  rw [hendpoint] at hcount_int
  have hcount :
      (lowerMechanicalWindowTrueCount alpha rho i n : Real) =
        ((⌊x + t⌋ : Int) : Real) - ((⌊x⌋ : Int) : Real) := by
    exact_mod_cast hcount_int
  have herror :
      (lowerMechanicalWindowTrueCount alpha rho i n : Real) - t =
        Int.fract x - Int.fract (x + t) := by
    rw [hcount]
    linarith [Int.floor_add_fract x, Int.floor_add_fract (x + t)]
  change |(lowerMechanicalWindowTrueCount alpha rho i n : Real) - t| < 1
  rw [herror, abs_lt]
  constructor
  · linarith [Int.fract_nonneg x, Int.fract_lt_one (x + t)]
  · linarith [Int.fract_lt_one x, Int.fract_nonneg (x + t)]

/- Every fixed-start lower-mechanical window has true-letter density alpha. -/
theorem lower_mechanical_window_true_density {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) (i : Nat) :
    Filter.Tendsto (fun n : Nat =>
      (lowerMechanicalWindowTrueCount alpha rho i n : Real) / n)
      Filter.atTop (nhds alpha) := by
  have hzero :
      Filter.Tendsto (fun n : Nat => (1 : Real) / n) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hlower :
      Filter.Tendsto (fun n : Nat => alpha - (1 : Real) / n)
        Filter.atTop (nhds alpha) := by
    simpa using tendsto_const_nhds.sub hzero
  have hupper :
      Filter.Tendsto (fun n : Nat => alpha + (1 : Real) / n)
        Filter.atTop (nhds alpha) := by
    simpa using tendsto_const_nhds.add hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with n hn
    have hn_pos : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hdisc := lower_mechanical_window_true_discrepancy
      (alpha := alpha) (rho := rho) halpha0 halpha1 i n
    rw [abs_lt] at hdisc
    have hl : (n : Real) * alpha - 1 ≤
        (lowerMechanicalWindowTrueCount alpha rho i n : Real) := by
      linarith
    calc
      alpha - (1 : Real) / n = ((n : Real) * alpha - 1) / n := by
        field_simp
      _ ≤ (lowerMechanicalWindowTrueCount alpha rho i n : Real) / n :=
        (div_le_div_iff_of_pos_right hn_pos).2 hl
  · filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with n hn
    have hn_pos : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hdisc := lower_mechanical_window_true_discrepancy
      (alpha := alpha) (rho := rho) halpha0 halpha1 i n
    rw [abs_lt] at hdisc
    have hu : (lowerMechanicalWindowTrueCount alpha rho i n : Real) ≤
        (n : Real) * alpha + 1 := by
      linarith
    calc
      (lowerMechanicalWindowTrueCount alpha rho i n : Real) / n ≤
          ((n : Real) * alpha + 1) / n :=
        (div_le_div_iff_of_pos_right hn_pos).2 hu
      _ = alpha + (1 : Real) / n := by
        field_simp

private theorem rational_lower_mechanical_window_discrepancy_example :
    |(lowerMechanicalWindowTrueCount (1 / 3 : Real) 0 0 3 : Real) -
      (3 : Real) * (1 / 3 : Real)| < 1 := by
  have hcount := lowerMechanicalWindowTrueCount_eq_floor
    (alpha := (1 / 3 : Real)) (rho := 0) (by norm_num) (by norm_num) 0 3
  have hcount' : lowerMechanicalWindowTrueCount (1 / 3 : Real) 0 0 3 = 1 := by
    norm_num at hcount
    exact_mod_cast hcount
  rw [hcount']
  norm_num

#print axioms lower_mechanical_window_true_discrepancy
#print axioms lower_mechanical_window_true_density

end D5.S1.Words.Mechanical
