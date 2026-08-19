/- GID: D5/S0/Tower/NodupAssembly/PeriodTen
   generality: I
   mirror-B: D5/B/S0/Tower/NodupAssembly/PeriodTen
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The period-ten representatives have pairwise distinct state codes. -/

import D5.S0.Tower.NodupAssembly.PeriodNine
import D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenDistinctB

/- Library-search audit trail (2026-08-18):
   * The adapter and the append lemma are reused from the period-nine assembly
     rather than restated, so there is one definition of each.
   * The concatenation is right associated, which is what `nodup_append` and
     `disjoint_append_right` expect; writing it left associated would need a
     different fold. -/

namespace D5.S0.Tower.NodupAssembly.PeriodTen

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenData
open D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenDistinctA
open D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenDistinctB
open D5.S0.Tower.NodupAssembly.PeriodNine

local notation "orbitStates" => tribonacciOrbitStates

/-- Tail from group ninth. -/
abbrev seg8 :=
  tribonacciPeriodTenOrbitsNinth.flatMap orbitStates

/-- Tail from group eighth. -/
abbrev seg7 :=
  tribonacciPeriodTenOrbitsEighth.flatMap orbitStates ++ seg8

/-- Tail from group seventh. -/
abbrev seg6 :=
  tribonacciPeriodTenOrbitsSeventh.flatMap orbitStates ++ seg7

/-- Tail from group sixth. -/
abbrev seg5 :=
  tribonacciPeriodTenOrbitsSixth.flatMap orbitStates ++ seg6

/-- Tail from group fifth. -/
abbrev seg4 :=
  tribonacciPeriodTenOrbitsFifth.flatMap orbitStates ++ seg5

/-- Tail from group fourth. -/
abbrev seg3 :=
  tribonacciPeriodTenOrbitsFourth.flatMap orbitStates ++ seg4

/-- Tail from group third. -/
abbrev seg2 :=
  tribonacciPeriodTenOrbitsThird.flatMap orbitStates ++ seg3

/-- Tail from group second. -/
abbrev seg1 :=
  tribonacciPeriodTenOrbitsSecond.flatMap orbitStates ++ seg2

/-- Tail from group first. -/
abbrev seg0 :=
  tribonacciPeriodTenOrbitsFirst.flatMap orbitStates ++ seg1

/-- No state code is shared by two of the forty-two period-ten
representatives. -/
theorem ten_all_codes_nodup : seg0.Nodup := by
  have h7 : (seg7).Nodup := by
    refine nodup_append_of_disjoint
      tribonacci_period_ten_eighth_state_codes_nodup
        tribonacci_period_ten_ninth_state_codes_nodup ?_
    exact tribonacci_period_ten_eighth_ninth_state_codes_disjoint
  have h6 : (seg6).Nodup := by
    refine nodup_append_of_disjoint
      tribonacci_period_ten_seventh_state_codes_nodup h7 ?_
    rw [List.disjoint_append_right]
    exact ⟨tribonacci_period_ten_seventh_eighth_state_codes_disjoint,
      tribonacci_period_ten_seventh_ninth_state_codes_disjoint⟩
  have h5 : (seg5).Nodup := by
    refine nodup_append_of_disjoint
      tribonacci_period_ten_sixth_state_codes_nodup h6 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨tribonacci_period_ten_sixth_seventh_state_codes_disjoint,
      tribonacci_period_ten_sixth_eighth_state_codes_disjoint,
      tribonacci_period_ten_sixth_ninth_state_codes_disjoint⟩
  have h4 : (seg4).Nodup := by
    refine nodup_append_of_disjoint
      tribonacci_period_ten_fifth_state_codes_nodup h5 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨tribonacci_period_ten_fifth_sixth_state_codes_disjoint,
      tribonacci_period_ten_fifth_seventh_state_codes_disjoint,
      tribonacci_period_ten_fifth_eighth_state_codes_disjoint,
      tribonacci_period_ten_fifth_ninth_state_codes_disjoint⟩
  have h3 : (seg3).Nodup := by
    refine nodup_append_of_disjoint
      tribonacci_period_ten_fourth_state_codes_nodup h4 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right]
    exact ⟨tribonacci_period_ten_fourth_fifth_state_codes_disjoint,
      tribonacci_period_ten_fourth_sixth_state_codes_disjoint,
      tribonacci_period_ten_fourth_seventh_state_codes_disjoint,
      tribonacci_period_ten_fourth_eighth_state_codes_disjoint,
      tribonacci_period_ten_fourth_ninth_state_codes_disjoint⟩
  have h2 : (seg2).Nodup := by
    refine nodup_append_of_disjoint
      tribonacci_period_ten_third_state_codes_nodup h3 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨tribonacci_period_ten_third_fourth_state_codes_disjoint,
      tribonacci_period_ten_third_fifth_state_codes_disjoint,
      tribonacci_period_ten_third_sixth_state_codes_disjoint,
      tribonacci_period_ten_third_seventh_state_codes_disjoint,
      tribonacci_period_ten_third_eighth_state_codes_disjoint,
      tribonacci_period_ten_third_ninth_state_codes_disjoint⟩
  have h1 : (seg1).Nodup := by
    refine nodup_append_of_disjoint
      tribonacci_period_ten_second_state_codes_nodup h2 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨tribonacci_period_ten_second_third_state_codes_disjoint,
      tribonacci_period_ten_second_fourth_state_codes_disjoint,
      tribonacci_period_ten_second_fifth_state_codes_disjoint,
      tribonacci_period_ten_second_sixth_state_codes_disjoint,
      tribonacci_period_ten_second_seventh_state_codes_disjoint,
      tribonacci_period_ten_second_eighth_state_codes_disjoint,
      tribonacci_period_ten_second_ninth_state_codes_disjoint⟩
  have h0 : (seg0).Nodup := by
    refine nodup_append_of_disjoint
      tribonacci_period_ten_first_state_codes_nodup h1 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right]
    exact ⟨tribonacci_period_ten_first_second_state_codes_disjoint,
      tribonacci_period_ten_first_third_state_codes_disjoint,
      tribonacci_period_ten_first_fourth_state_codes_disjoint,
      tribonacci_period_ten_first_fifth_state_codes_disjoint,
      tribonacci_period_ten_first_sixth_state_codes_disjoint,
      tribonacci_period_ten_first_seventh_state_codes_disjoint,
      tribonacci_period_ten_first_eighth_state_codes_disjoint,
      tribonacci_period_ten_first_ninth_state_codes_disjoint⟩
  exact h0

end D5.S0.Tower.NodupAssembly.PeriodTen
