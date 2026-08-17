/- GID: D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicCompleteness
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacciGeneral/TribonacciPeriodicCompleteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Ten coded cycles exhaust every real Tribonacci periodic state through period five. -/

import D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration

namespace D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicCompleteness

local notation "pointCodes" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciPeriodicPointCodesFive
local notation "representatives" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciPeriodicOrbitRepresentativesFive
local notation "championOrbit" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciChampionPeriodicOrbit
local notation "orbitStates" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciOrbitStates
local notation "enumeratedStates" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciEnumeratedOrbitStatesFive
local notation "decodedOrbitStates" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciDecodedOrbitStates
local notation "makeOrbit" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit
local notation "traceCode" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciTraceCode
local notation "applyStepsCode" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepsCode
local notation "applyStepCode" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode
local notation "stateCodesNodup" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacci_periodic_orbit_state_codes_nodup
local notation "pointComplete" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacci_periodic_point_enumeration_complete_five
local notation "transition" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition

abbrev CodedState :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.CodedState

abbrev PeriodicState :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.PeriodicState

/- Library-search audit trail (2026-08-17):
   * Repository search found no prior finite Tribonacci coverage theorem.
   * The imported generator proves the reverse branch-word map; this module
     closes the finite computation by equating its fixed points with the ten
     disjoint explicit cycles. No external theorem is used. -/

set_option maxHeartbeats 1000000 in
-- Expanding all forty-three generated fixed-point equations exceeds the default budget.
/-- The ten displayed cycles contain exactly the same coded states as all
fixed-point equations through period five. -/
theorem tribonacci_enumerated_orbit_states_eq_fixed_points :
    enumeratedStates = pointCodes := by
  apply Finset.ext
  intro code
  rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciEnumeratedOrbitStatesFive,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciPeriodicPointCodesFive]
  simp only [List.mem_toFinset]
  simp [List.range_succ,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciPeriodicOrbitRepresentativesFive,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciChampionPeriodicOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciOrbitStates,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciTraceCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciFixedPointCodes,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciClosedItineraries,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciClosedFrom,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathsFrom]
  norm_num [
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepsCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciApplyStepCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathCandidateCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciAffineCompose,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciIdentityAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepTarget,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeDiv,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeInv,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeNorm,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeCofactorZero,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeCofactorOne,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeCofactorTwo,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeSub,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeNeg,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeAdd,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeMul,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeOne,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeZero,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot]
  aesop

/-- Ten disjoint cycles with thirty-seven phase states form the complete coded
partition through period five. -/
theorem tribonacci_periodic_orbit_partition_five :
    (representatives).length = 10 ∧ (enumeratedStates).card = 37 := by
  constructor
  · norm_num [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciPeriodicOrbitRepresentativesFive]
  · change ((representatives).flatMap orbitStates).toFinset.card = 37
    calc
      _ = ((representatives).flatMap orbitStates).length :=
        List.toFinset_card_of_nodup stateCodesNodup
      _ = 37 := by
        norm_num [
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciPeriodicOrbitRepresentativesFive,
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciChampionPeriodicOrbit,
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciMakeOrbit,
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciOrbitStates,
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciTraceCode]

/-- Orbit-level completeness: every real state fixed by a nonzero iterate at
most five lies on one of the ten displayed decoded cycles. -/
theorem tribonacci_periodic_orbit_enumeration_complete_five {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 5)
    (state : PeriodicState)
    (hperiod : (transition^[period]) state = state) :
    ∃ orbit ∈ representatives, state ∈ decodedOrbitStates orbit := by
  obtain ⟨code, hcode, rfl⟩ :=
    pointComplete hperiodPos hperiodBound state hperiod
  have henumerated : code ∈ enumeratedStates := by
    rw [tribonacci_enumerated_orbit_states_eq_fixed_points]
    exact hcode
  rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciEnumeratedOrbitStatesFive,
    List.mem_toFinset] at henumerated
  simp only [List.mem_flatMap] at henumerated
  obtain ⟨orbit, horbit, hcodeOrbit⟩ := henumerated
  refine ⟨orbit, horbit, ?_⟩
  rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacciDecodedOrbitStates,
    List.mem_map]
  exact ⟨code, hcodeOrbit, rfl⟩

end D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicCompleteness
