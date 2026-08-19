/- GID: D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineAggregate
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicNine/EnumerationNineAggregate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The period-at-most-nine enumeration has maximin exactly the champion value. -/

import D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineMaximinB

/- Library-search audit trail (2026-08-18):
   * The period-nine level already carries validity, per-orbit low-arm bounds and
     pairwise distinctness.  What it does not carry is the shape the aggregate
     maximin statement consumes: a cumulative representative list, and the
     membership of each low state in its own orbit.  Those two are added here.
   * The period-eight level is the template; its cumulative list is the
     period-seven one appended with the exactly-eight certificates, and its
     membership lemma is one `norm_num` over the orbit definitions.
   * The optimality statement itself is the point: twenty-six per-orbit bounds
     and the period-eight aggregate were all in the tree, but the conjunction
     over the cumulative list was not written, so the source sentence's claim at
     periods beyond eight had no formal counterpart. -/

namespace D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineAggregate

open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin
open D5.S0.Tower.TribonacciPeriodic.EnumerationSixData
open D5.S0.Tower.TribonacciPeriodic.EnumerationSeven
open D5.S0.Tower.TribonacciPeriodic.EnumerationSevenData
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEight
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightData
open D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineData
open D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineMaximinA
open D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineMaximinB

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant
local notation "transition" => tribonacciPeriodicTransition
local notation "orbitStates" => tribonacciOrbitStates
local notation "decodedOrbitStates" => tribonacciDecodedOrbitStates

/-- The twenty-six primitive period-nine rotation classes, as one list. -/
def tribonacciPeriodicOrbitRepresentativesExactlyNine : List TribonacciCodedOrbit :=
  [tribonacciPeriodNineOrbitA, tribonacciPeriodNineOrbitB, tribonacciPeriodNineOrbitC,
    tribonacciPeriodNineOrbitD, tribonacciPeriodNineOrbitE, tribonacciPeriodNineOrbitF,
    tribonacciPeriodNineOrbitG, tribonacciPeriodNineOrbitH, tribonacciPeriodNineOrbitI,
    tribonacciPeriodNineOrbitJ, tribonacciPeriodNineOrbitK, tribonacciPeriodNineOrbitL,
    tribonacciPeriodNineOrbitM, tribonacciPeriodNineOrbitN, tribonacciPeriodNineOrbitO,
    tribonacciPeriodNineOrbitP, tribonacciPeriodNineOrbitQ, tribonacciPeriodNineOrbitR,
    tribonacciPeriodNineOrbitS, tribonacciPeriodNineOrbitT, tribonacciPeriodNineOrbitU,
    tribonacciPeriodNineOrbitV, tribonacciPeriodNineOrbitW, tribonacciPeriodNineOrbitX,
    tribonacciPeriodNineOrbitY, tribonacciPeriodNineOrbitZ]

/-- The cumulative list through period nine. -/
def tribonacciPeriodicOrbitRepresentativesNine : List TribonacciCodedOrbit :=
  tribonacciPeriodicOrbitRepresentativesEight ++
    tribonacciPeriodicOrbitRepresentativesExactlyNine

/-- Each new certificate's recorded low state really is one of its own states. -/
theorem tribonacci_new_periodic_orbit_low_states_mem_nine :
    tribonacciPeriodicOrbitRepresentativesExactlyNine.Forall fun orbit =>
      orbit.lowState ∈ orbitStates orbit := by
  norm_num [tribonacciPeriodicOrbitRepresentativesExactlyNine,
    tribonacciPeriodNineOrbitA, tribonacciPeriodNineOrbitB, tribonacciPeriodNineOrbitC,
    tribonacciPeriodNineOrbitD, tribonacciPeriodNineOrbitE, tribonacciPeriodNineOrbitF,
    tribonacciPeriodNineOrbitG, tribonacciPeriodNineOrbitH, tribonacciPeriodNineOrbitI,
    tribonacciPeriodNineOrbitJ, tribonacciPeriodNineOrbitK, tribonacciPeriodNineOrbitL,
    tribonacciPeriodNineOrbitM, tribonacciPeriodNineOrbitN, tribonacciPeriodNineOrbitO,
    tribonacciPeriodNineOrbitP, tribonacciPeriodNineOrbitQ, tribonacciPeriodNineOrbitR,
    tribonacciPeriodNineOrbitS, tribonacciPeriodNineOrbitT, tribonacciPeriodNineOrbitU,
    tribonacciPeriodNineOrbitV, tribonacciPeriodNineOrbitW, tribonacciPeriodNineOrbitX,
    tribonacciPeriodNineOrbitY, tribonacciPeriodNineOrbitZ, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode, tribonacciApplyStepsCode,
    tribonacciApplyStepCode]

/-- Every new certificate's low arm is bounded by the champion value. -/
theorem tribonacci_new_periodic_orbit_low_arms_bounded_nine :
    tribonacciPeriodicOrbitRepresentativesExactlyNine.Forall fun orbit =>
      tribonacciPeriodicStateArm (decodeTribonacciState orbit.lowState) ≤
        championValue t := by
  simp only [tribonacciPeriodicOrbitRepresentativesExactlyNine, List.forall_cons]
  exact ⟨tribonacci_period_nine_orbit_a_low_arm, tribonacci_period_nine_orbit_b_low_arm,
    tribonacci_period_nine_orbit_c_low_arm, tribonacci_period_nine_orbit_d_low_arm,
    tribonacci_period_nine_orbit_e_low_arm, tribonacci_period_nine_orbit_f_low_arm,
    tribonacci_period_nine_orbit_g_low_arm, tribonacci_period_nine_orbit_h_low_arm,
    tribonacci_period_nine_orbit_i_low_arm, tribonacci_period_nine_orbit_j_low_arm,
    tribonacci_period_nine_orbit_k_low_arm, tribonacci_period_nine_orbit_l_low_arm,
    tribonacci_period_nine_orbit_m_low_arm, tribonacci_period_nine_orbit_n_low_arm,
    tribonacci_period_nine_orbit_o_low_arm, tribonacci_period_nine_orbit_p_low_arm,
    tribonacci_period_nine_orbit_q_low_arm, tribonacci_period_nine_orbit_r_low_arm,
    tribonacci_period_nine_orbit_s_low_arm, tribonacci_period_nine_orbit_t_low_arm,
    tribonacci_period_nine_orbit_u_low_arm, tribonacci_period_nine_orbit_v_low_arm,
    tribonacci_period_nine_orbit_w_low_arm, tribonacci_period_nine_orbit_x_low_arm,
    tribonacci_period_nine_orbit_y_low_arm, tribonacci_period_nine_orbit_z_low_arm, trivial⟩

/-- Both properties lift to the cumulative list. -/
theorem tribonacci_periodic_orbit_low_states_mem_nine :
    tribonacciPeriodicOrbitRepresentativesNine.Forall fun orbit =>
      orbit.lowState ∈ orbitStates orbit := by
  rw [tribonacciPeriodicOrbitRepresentativesNine, List.forall_append]
  exact ⟨tribonacci_periodic_orbit_low_states_mem_eight,
    tribonacci_new_periodic_orbit_low_states_mem_nine⟩

theorem tribonacci_periodic_orbit_low_arms_bounded_nine :
    tribonacciPeriodicOrbitRepresentativesNine.Forall fun orbit =>
      tribonacciPeriodicStateArm (decodeTribonacciState orbit.lowState) ≤
        championValue t := by
  rw [tribonacciPeriodicOrbitRepresentativesNine, List.forall_append]
  exact ⟨tribonacci_periodic_orbit_low_arms_bounded_eight,
    tribonacci_new_periodic_orbit_low_arms_bounded_nine⟩

/-- The minima attained across the cumulative period-at-most-nine enumeration. -/
def tribonacciPeriodicOrbitMinimaNine : Set Real :=
  {value | ∃ orbit ∈ tribonacciPeriodicOrbitRepresentativesNine,
    TribonacciOrbitMinimum orbit value}

/-- The complete period-at-most-nine enumeration has maximin exactly
`championValue t`, attained by the period-two repeating `ba` orbit. -/
theorem tribonacci_periodic_orbit_maximin_nine :
    IsGreatest tribonacciPeriodicOrbitMinimaNine (championValue t) := by
  constructor
  · refine ⟨tribonacciChampionPeriodicOrbit, ?_,
      tribonacci_champion_periodic_orbit_minimum⟩
    simp [tribonacciPeriodicOrbitRepresentativesNine,
      tribonacciPeriodicOrbitRepresentativesEight,
      tribonacciPeriodicOrbitRepresentativesSeven,
      D5.S0.Tower.TribonacciPeriodic.EnumerationSixData.tribonacciPeriodicOrbitRepresentativesSix,
      tribonacciPeriodicOrbitRepresentativesFive]
  · rintro value ⟨orbit, horbit, hminimum⟩
    have hlowCode := List.forall_iff_forall_mem.mp
      tribonacci_periodic_orbit_low_states_mem_nine orbit horbit
    have hlowDecoded : decodeTribonacciState orbit.lowState ∈
        decodedOrbitStates orbit := by
      rw [tribonacciDecodedOrbitStates, List.mem_map]
      exact ⟨orbit.lowState, hlowCode, rfl⟩
    have hvalueLow := hminimum.1 _ hlowDecoded
    have hlowBound := List.forall_iff_forall_mem.mp
      tribonacci_periodic_orbit_low_arms_bounded_nine orbit horbit
    exact hvalueLow.trans hlowBound

end D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineAggregate
