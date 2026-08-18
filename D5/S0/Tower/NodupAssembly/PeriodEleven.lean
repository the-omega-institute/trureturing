/- GID: D5/S0/Tower/NodupAssembly/PeriodEleven
   generality: I
   mirror-B: D5/B/S0/Tower/NodupAssembly/PeriodEleven
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The period-eleven representatives have pairwise distinct state codes. -/

import D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartD
import D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartE
import D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartF

/- Library-search audit trail (2026-08-18):
   * Pinned Mathlib's `List.Nodup.append` takes the three hypotheses directly,
     so no local adapter is needed here.  The period-nine and period-ten
     assemblies restate it as `nodup_append_of_disjoint`; that duplication is
     recorded in issue 2419 and is not propagated to this level.
   * Nineteen groups here rather than nine, because the period-eleven level is
     grouped by four; the fold is the same shape, only longer.
   * The concatenation is right associated, which is what `nodup_append` and
     `disjoint_append_right` expect. -/

namespace D5.S0.Tower.NodupAssembly.PeriodEleven

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenData
open D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartA
open D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartB
open D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartC
open D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartD
open D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartE
open D5.S0.Tower.TribonacciPeriodicElevenDistinct.PartF

local notation "orbitStates" => tribonacciOrbitStates

/-- Tail from group nineteen. -/
abbrev seg18 :=
  elevenOrbitsG19.flatMap orbitStates

/-- Tail from group 18. -/
abbrev seg17 :=
  elevenOrbitsG18.flatMap orbitStates ++ seg18

/-- Tail from group 17. -/
abbrev seg16 :=
  elevenOrbitsG17.flatMap orbitStates ++ seg17

/-- Tail from group 16. -/
abbrev seg15 :=
  elevenOrbitsG16.flatMap orbitStates ++ seg16

/-- Tail from group 15. -/
abbrev seg14 :=
  elevenOrbitsG15.flatMap orbitStates ++ seg15

/-- Tail from group 14. -/
abbrev seg13 :=
  elevenOrbitsG14.flatMap orbitStates ++ seg14

/-- Tail from group 13. -/
abbrev seg12 :=
  elevenOrbitsG13.flatMap orbitStates ++ seg13

/-- Tail from group 12. -/
abbrev seg11 :=
  elevenOrbitsG12.flatMap orbitStates ++ seg12

/-- Tail from group 11. -/
abbrev seg10 :=
  elevenOrbitsG11.flatMap orbitStates ++ seg11

/-- Tail from group 10. -/
abbrev seg9 :=
  elevenOrbitsG10.flatMap orbitStates ++ seg10

/-- Tail from group 09. -/
abbrev seg8 :=
  elevenOrbitsG09.flatMap orbitStates ++ seg9

/-- Tail from group 08. -/
abbrev seg7 :=
  elevenOrbitsG08.flatMap orbitStates ++ seg8

/-- Tail from group 07. -/
abbrev seg6 :=
  elevenOrbitsG07.flatMap orbitStates ++ seg7

/-- Tail from group 06. -/
abbrev seg5 :=
  elevenOrbitsG06.flatMap orbitStates ++ seg6

/-- Tail from group 05. -/
abbrev seg4 :=
  elevenOrbitsG05.flatMap orbitStates ++ seg5

/-- Tail from group 04. -/
abbrev seg3 :=
  elevenOrbitsG04.flatMap orbitStates ++ seg4

/-- Tail from group 03. -/
abbrev seg2 :=
  elevenOrbitsG03.flatMap orbitStates ++ seg3

/-- Tail from group 02. -/
abbrev seg1 :=
  elevenOrbitsG02.flatMap orbitStates ++ seg2

/-- Tail from group 01. -/
abbrev seg0 :=
  elevenOrbitsG01.flatMap orbitStates ++ seg1

/-- Every state code among the seventy-four period-eleven representatives is distinct. -/
theorem tribonacci_period_eleven_state_codes_nodup : (seg0).Nodup := by
  have h18 : (seg18).Nodup := eleven_g19_state_codes_nodup
  have h17 : (seg17).Nodup := by
    refine List.Nodup.append
      eleven_g18_state_codes_nodup h18 ?_
    exact eleven_g18_g19_state_codes_disjoint
  have h16 : (seg16).Nodup := by
    refine List.Nodup.append
      eleven_g17_state_codes_nodup h17 ?_
    rw [List.disjoint_append_right]
    exact ⟨eleven_g17_g18_state_codes_disjoint, eleven_g17_g19_state_codes_disjoint⟩
  have h15 : (seg15).Nodup := by
    refine List.Nodup.append
      eleven_g16_state_codes_nodup h16 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨eleven_g16_g17_state_codes_disjoint, eleven_g16_g18_state_codes_disjoint,
      eleven_g16_g19_state_codes_disjoint⟩
  have h14 : (seg14).Nodup := by
    refine List.Nodup.append
      eleven_g15_state_codes_nodup h15 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨eleven_g15_g16_state_codes_disjoint, eleven_g15_g17_state_codes_disjoint,
      eleven_g15_g18_state_codes_disjoint, eleven_g15_g19_state_codes_disjoint⟩
  have h13 : (seg13).Nodup := by
    refine List.Nodup.append
      eleven_g14_state_codes_nodup h14 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right]
    exact ⟨eleven_g14_g15_state_codes_disjoint, eleven_g14_g16_state_codes_disjoint,
      eleven_g14_g17_state_codes_disjoint, eleven_g14_g18_state_codes_disjoint,
      eleven_g14_g19_state_codes_disjoint⟩
  have h12 : (seg12).Nodup := by
    refine List.Nodup.append
      eleven_g13_state_codes_nodup h13 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨eleven_g13_g14_state_codes_disjoint, eleven_g13_g15_state_codes_disjoint,
      eleven_g13_g16_state_codes_disjoint, eleven_g13_g17_state_codes_disjoint,
      eleven_g13_g18_state_codes_disjoint, eleven_g13_g19_state_codes_disjoint⟩
  have h11 : (seg11).Nodup := by
    refine List.Nodup.append
      eleven_g12_state_codes_nodup h12 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨eleven_g12_g13_state_codes_disjoint, eleven_g12_g14_state_codes_disjoint,
      eleven_g12_g15_state_codes_disjoint, eleven_g12_g16_state_codes_disjoint,
      eleven_g12_g17_state_codes_disjoint, eleven_g12_g18_state_codes_disjoint,
      eleven_g12_g19_state_codes_disjoint⟩
  have h10 : (seg10).Nodup := by
    refine List.Nodup.append
      eleven_g11_state_codes_nodup h11 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right]
    exact ⟨eleven_g11_g12_state_codes_disjoint, eleven_g11_g13_state_codes_disjoint,
      eleven_g11_g14_state_codes_disjoint, eleven_g11_g15_state_codes_disjoint,
      eleven_g11_g16_state_codes_disjoint, eleven_g11_g17_state_codes_disjoint,
      eleven_g11_g18_state_codes_disjoint, eleven_g11_g19_state_codes_disjoint⟩
  have h9 : (seg9).Nodup := by
    refine List.Nodup.append
      eleven_g10_state_codes_nodup h10 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨eleven_g10_g11_state_codes_disjoint, eleven_g10_g12_state_codes_disjoint,
      eleven_g10_g13_state_codes_disjoint, eleven_g10_g14_state_codes_disjoint,
      eleven_g10_g15_state_codes_disjoint, eleven_g10_g16_state_codes_disjoint,
      eleven_g10_g17_state_codes_disjoint, eleven_g10_g18_state_codes_disjoint,
      eleven_g10_g19_state_codes_disjoint⟩
  have h8 : (seg8).Nodup := by
    refine List.Nodup.append
      eleven_g09_state_codes_nodup h9 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨eleven_g09_g10_state_codes_disjoint, eleven_g09_g11_state_codes_disjoint,
      eleven_g09_g12_state_codes_disjoint, eleven_g09_g13_state_codes_disjoint,
      eleven_g09_g14_state_codes_disjoint, eleven_g09_g15_state_codes_disjoint,
      eleven_g09_g16_state_codes_disjoint, eleven_g09_g17_state_codes_disjoint,
      eleven_g09_g18_state_codes_disjoint, eleven_g09_g19_state_codes_disjoint⟩
  have h7 : (seg7).Nodup := by
    refine List.Nodup.append
      eleven_g08_state_codes_nodup h8 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right]
    exact ⟨eleven_g08_g09_state_codes_disjoint, eleven_g08_g10_state_codes_disjoint,
      eleven_g08_g11_state_codes_disjoint, eleven_g08_g12_state_codes_disjoint,
      eleven_g08_g13_state_codes_disjoint, eleven_g08_g14_state_codes_disjoint,
      eleven_g08_g15_state_codes_disjoint, eleven_g08_g16_state_codes_disjoint,
      eleven_g08_g17_state_codes_disjoint, eleven_g08_g18_state_codes_disjoint,
      eleven_g08_g19_state_codes_disjoint⟩
  have h6 : (seg6).Nodup := by
    refine List.Nodup.append
      eleven_g07_state_codes_nodup h7 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨eleven_g07_g08_state_codes_disjoint, eleven_g07_g09_state_codes_disjoint,
      eleven_g07_g10_state_codes_disjoint, eleven_g07_g11_state_codes_disjoint,
      eleven_g07_g12_state_codes_disjoint, eleven_g07_g13_state_codes_disjoint,
      eleven_g07_g14_state_codes_disjoint, eleven_g07_g15_state_codes_disjoint,
      eleven_g07_g16_state_codes_disjoint, eleven_g07_g17_state_codes_disjoint,
      eleven_g07_g18_state_codes_disjoint, eleven_g07_g19_state_codes_disjoint⟩
  have h5 : (seg5).Nodup := by
    refine List.Nodup.append
      eleven_g06_state_codes_nodup h6 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨eleven_g06_g07_state_codes_disjoint, eleven_g06_g08_state_codes_disjoint,
      eleven_g06_g09_state_codes_disjoint, eleven_g06_g10_state_codes_disjoint,
      eleven_g06_g11_state_codes_disjoint, eleven_g06_g12_state_codes_disjoint,
      eleven_g06_g13_state_codes_disjoint, eleven_g06_g14_state_codes_disjoint,
      eleven_g06_g15_state_codes_disjoint, eleven_g06_g16_state_codes_disjoint,
      eleven_g06_g17_state_codes_disjoint, eleven_g06_g18_state_codes_disjoint,
      eleven_g06_g19_state_codes_disjoint⟩
  have h4 : (seg4).Nodup := by
    refine List.Nodup.append
      eleven_g05_state_codes_nodup h5 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right]
    exact ⟨eleven_g05_g06_state_codes_disjoint, eleven_g05_g07_state_codes_disjoint,
      eleven_g05_g08_state_codes_disjoint, eleven_g05_g09_state_codes_disjoint,
      eleven_g05_g10_state_codes_disjoint, eleven_g05_g11_state_codes_disjoint,
      eleven_g05_g12_state_codes_disjoint, eleven_g05_g13_state_codes_disjoint,
      eleven_g05_g14_state_codes_disjoint, eleven_g05_g15_state_codes_disjoint,
      eleven_g05_g16_state_codes_disjoint, eleven_g05_g17_state_codes_disjoint,
      eleven_g05_g18_state_codes_disjoint, eleven_g05_g19_state_codes_disjoint⟩
  have h3 : (seg3).Nodup := by
    refine List.Nodup.append
      eleven_g04_state_codes_nodup h4 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨eleven_g04_g05_state_codes_disjoint, eleven_g04_g06_state_codes_disjoint,
      eleven_g04_g07_state_codes_disjoint, eleven_g04_g08_state_codes_disjoint,
      eleven_g04_g09_state_codes_disjoint, eleven_g04_g10_state_codes_disjoint,
      eleven_g04_g11_state_codes_disjoint, eleven_g04_g12_state_codes_disjoint,
      eleven_g04_g13_state_codes_disjoint, eleven_g04_g14_state_codes_disjoint,
      eleven_g04_g15_state_codes_disjoint, eleven_g04_g16_state_codes_disjoint,
      eleven_g04_g17_state_codes_disjoint, eleven_g04_g18_state_codes_disjoint,
      eleven_g04_g19_state_codes_disjoint⟩
  have h2 : (seg2).Nodup := by
    refine List.Nodup.append
      eleven_g03_state_codes_nodup h3 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨eleven_g03_g04_state_codes_disjoint, eleven_g03_g05_state_codes_disjoint,
      eleven_g03_g06_state_codes_disjoint, eleven_g03_g07_state_codes_disjoint,
      eleven_g03_g08_state_codes_disjoint, eleven_g03_g09_state_codes_disjoint,
      eleven_g03_g10_state_codes_disjoint, eleven_g03_g11_state_codes_disjoint,
      eleven_g03_g12_state_codes_disjoint, eleven_g03_g13_state_codes_disjoint,
      eleven_g03_g14_state_codes_disjoint, eleven_g03_g15_state_codes_disjoint,
      eleven_g03_g16_state_codes_disjoint, eleven_g03_g17_state_codes_disjoint,
      eleven_g03_g18_state_codes_disjoint, eleven_g03_g19_state_codes_disjoint⟩
  have h1 : (seg1).Nodup := by
    refine List.Nodup.append
      eleven_g02_state_codes_nodup h2 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right]
    exact ⟨eleven_g02_g03_state_codes_disjoint, eleven_g02_g04_state_codes_disjoint,
      eleven_g02_g05_state_codes_disjoint, eleven_g02_g06_state_codes_disjoint,
      eleven_g02_g07_state_codes_disjoint, eleven_g02_g08_state_codes_disjoint,
      eleven_g02_g09_state_codes_disjoint, eleven_g02_g10_state_codes_disjoint,
      eleven_g02_g11_state_codes_disjoint, eleven_g02_g12_state_codes_disjoint,
      eleven_g02_g13_state_codes_disjoint, eleven_g02_g14_state_codes_disjoint,
      eleven_g02_g15_state_codes_disjoint, eleven_g02_g16_state_codes_disjoint,
      eleven_g02_g17_state_codes_disjoint, eleven_g02_g18_state_codes_disjoint,
      eleven_g02_g19_state_codes_disjoint⟩
  have h0 : (seg0).Nodup := by
    refine List.Nodup.append
      eleven_g01_state_codes_nodup h1 ?_
    rw [List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right, List.disjoint_append_right,
      List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨eleven_g01_g02_state_codes_disjoint, eleven_g01_g03_state_codes_disjoint,
      eleven_g01_g04_state_codes_disjoint, eleven_g01_g05_state_codes_disjoint,
      eleven_g01_g06_state_codes_disjoint, eleven_g01_g07_state_codes_disjoint,
      eleven_g01_g08_state_codes_disjoint, eleven_g01_g09_state_codes_disjoint,
      eleven_g01_g10_state_codes_disjoint, eleven_g01_g11_state_codes_disjoint,
      eleven_g01_g12_state_codes_disjoint, eleven_g01_g13_state_codes_disjoint,
      eleven_g01_g14_state_codes_disjoint, eleven_g01_g15_state_codes_disjoint,
      eleven_g01_g16_state_codes_disjoint, eleven_g01_g17_state_codes_disjoint,
      eleven_g01_g18_state_codes_disjoint, eleven_g01_g19_state_codes_disjoint⟩
  exact h0

end D5.S0.Tower.NodupAssembly.PeriodEleven
