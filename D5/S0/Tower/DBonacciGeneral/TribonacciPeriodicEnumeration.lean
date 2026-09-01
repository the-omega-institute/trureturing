/- GID: D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact period-at-most-five Tribonacci orbit representatives and validity proofs. -/

import D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
import D5.S0.Tower.DBonacciGeneral.ChampionValue

namespace D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant
local notation "transition" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition
local notation "generatorComplete" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacci_periodic_point_enumeration_complete

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen champion value and orbit, and the open
     PR #2241 supplied the golden period-seven certificate shape. No existing
     Tribonacci finite-period enumeration was present on `origin/dev`.
   * Pinned mathlib supplies decidable finite lists and elementary real
     inequalities. The ten orbit representatives below are generated from the
     exact cubic fixed-point equations rather than imported numerics. -/

abbrev Gap :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicGap

abbrev Step :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicStep

abbrev Code :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciCubicCode

abbrev CodedState :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciCodedState

abbrev PeriodicState :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicState

def tribonacciClosedItinerariesFive : List (Gap × List Step) :=
  (List.range 5).flatMap fun period =>
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciClosedItineraries
      (period + 1)

def tribonacciPeriodicPointCodesFive : Finset CodedState :=
  ((List.range 5).flatMap fun period =>
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciFixedPointCodes
      (period + 1)).toFinset

/-- The closed-walk generator has the displayed number of phase-marked fixed
point equations at each period through five. -/
theorem tribonacci_fixed_point_counts_through_five :
    (List.range 5).map (fun period =>
      (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciFixedPointCodes
        (period + 1)).length) = [1, 3, 7, 11, 21] := by
  decide

/-- Every denominator occurring through period five is nonzero in `Q(t)`. -/
theorem tribonacci_closed_itinerary_denominators_five :
    tribonacciClosedItinerariesFive.Forall fun itinerary =>
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeNorm
        (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeSub
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeOne
          (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine
            itinerary.2).multiplier) ≠ 0 := by
  set_option maxRecDepth 100000 in
    have hrange : List.range 5 = [0, 1, 2, 3, 4] := by decide
    rw [tribonacciClosedItinerariesFive, hrange]
    simp [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciClosedItineraries,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciClosedFrom,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathsFrom]
    norm_num [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciAffineCompose,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciIdentityAffine,
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

/-- Point-level completeness through period five, including the reverse map
from every real branch orbit to its generated exact cubic fixed point. -/
theorem tribonacci_periodic_point_enumeration_complete_five {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 5)
    (state : PeriodicState)
    (hperiod : (transition^[period]) state = state) :
    ∃ code ∈ tribonacciPeriodicPointCodesFive,
      state =
        D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState code := by
  obtain ⟨index, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hperiodPos)
  have hindex : index < 5 := by omega
  let steps :=
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciActualSteps
      (index + 1) state
  have hitinerary : (state.kind, steps) ∈
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciClosedItineraries
        (index + 1) :=
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacci_actual_steps_mem_closed
      hperiod
  have hitineraryFive : (state.kind, steps) ∈ tribonacciClosedItinerariesFive := by
    simp only [tribonacciClosedItinerariesFive, List.mem_flatMap]
    exact ⟨index, List.mem_range.mpr hindex, hitinerary⟩
  have hnorm := List.forall_iff_forall_mem.mp
    tribonacci_closed_itinerary_denominators_five (state.kind, steps) hitineraryFive
  obtain ⟨code, hcode, hdecode⟩ :=
    generatorComplete state hperiod hnorm
  refine ⟨code, ?_, hdecode⟩
  rw [tribonacciPeriodicPointCodesFive, List.mem_toFinset]
  simp only [List.mem_flatMap]
  exact ⟨index, List.mem_range.mpr hindex, hcode⟩

def tribonacciApplyStepCode (state : CodedState) (step : Step) : CodedState :=
  let affine :=
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine step
  ⟨D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepTarget step,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeAdd
      (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeMul
        affine.multiplier state.coordinate) affine.offset⟩

def tribonacciApplyStepsCode : CodedState → List Step → CodedState
  | state, [] => state
  | state, step :: rest =>
      tribonacciApplyStepsCode (tribonacciApplyStepCode state step) rest

def tribonacciTraceCode : CodedState → List Step → List CodedState
  | _, [] => []
  | state, step :: rest =>
      state :: tribonacciTraceCode (tribonacciApplyStepCode state step) rest

def tribonacciCodedStateInGap (state : CodedState) : Prop :=
  0 ≤ D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue
      state.coordinate ∧
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue
      state.coordinate ≤
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength
        state.kind

def tribonacciCodedStepValid (state : CodedState) (step : Step) : Prop :=
  state.kind =
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepSource step ∧
    match step with
    | .smallThrough => True
    | .combinedLeft | .largeLeft =>
        D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue
          state.coordinate ≤ t⁻¹
    | .combinedRight | .largeRight =>
        t⁻¹ <
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue
            state.coordinate

def tribonacciCodedTraceValid : CodedState → List Step → Prop
  | _, [] => True
  | state, step :: rest =>
      tribonacciCodedStateInGap state ∧
        tribonacciCodedStepValid state step ∧
        tribonacciCodedTraceValid (tribonacciApplyStepCode state step) rest

theorem tribonacci_decode_step {state : CodedState} {step : Step}
    (hvalid : tribonacciCodedStepValid state step) :
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition
        (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState state) =
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState
        (tribonacciApplyStepCode state step) := by
  rcases state with ⟨kind, coordinate⟩
  cases step <;>
    rcases hvalid with ⟨hkind, hbranch⟩ <;>
    simp only [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepSource]
      at hkind <;>
    subst kind
  · rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition.eq_1,
      show (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState
        ({kind := .small, coordinate := coordinate} : CodedState)).kind = .small by rfl]
    simp only [tribonacciApplyStepCode,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepTarget,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine]
    congr 1
    rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacci_code_value_add,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacci_code_value_mul]
    norm_num [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeZero]
  · rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition.eq_1,
      show (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState
        ({kind := .combined, coordinate := coordinate} : CodedState)).kind = .combined by rfl]
    have hbranch' :
        (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState
          ({kind := .combined, coordinate := coordinate} : CodedState)).coordinate ≤ t⁻¹ := by
      change D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue
          coordinate ≤ t⁻¹
      exact hbranch
    simp only [if_pos hbranch']
    simp only [tribonacciApplyStepCode,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepTarget,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine]
    congr 1
    rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacci_code_value_add,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacci_code_value_mul]
    norm_num [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeZero]
  · rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition.eq_1,
      show (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState
        ({kind := .combined, coordinate := coordinate} : CodedState)).kind = .combined by rfl]
    have hbranch' : t⁻¹ <
        (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState
          ({kind := .combined, coordinate := coordinate} : CodedState)).coordinate := by
      change t⁻¹ <
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue
            coordinate
      exact hbranch
    simp only [if_neg (not_le_of_gt hbranch')]
    simp only [tribonacciApplyStepCode,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepTarget,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine]
    congr 1
    rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacci_code_value_add,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacci_code_value_mul,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacci_code_value_neg]
    norm_num [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeOne]
    ring
  · rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition.eq_1,
      show (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState
        ({kind := .large, coordinate := coordinate} : CodedState)).kind = .large by rfl]
    have hbranch' :
        (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState
          ({kind := .large, coordinate := coordinate} : CodedState)).coordinate ≤ t⁻¹ := by
      change D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue
          coordinate ≤ t⁻¹
      exact hbranch
    simp only [if_pos hbranch']
    simp only [tribonacciApplyStepCode,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepTarget,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine]
    congr 1
    rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacci_code_value_add,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacci_code_value_mul]
    norm_num [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeZero]
  · rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition.eq_1,
      show (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState
        ({kind := .large, coordinate := coordinate} : CodedState)).kind = .large by rfl]
    have hbranch' : t⁻¹ <
        (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState
          ({kind := .large, coordinate := coordinate} : CodedState)).coordinate := by
      change t⁻¹ <
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue
            coordinate
      exact hbranch
    simp only [if_neg (not_le_of_gt hbranch')]
    simp only [tribonacciApplyStepCode,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepTarget,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine]
    congr 1
    rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacci_code_value_add,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacci_code_value_mul,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacci_code_value_neg]
    norm_num [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeOne]
    ring

theorem tribonacci_decode_steps {state : CodedState} {steps : List Step}
    (hvalid : tribonacciCodedTraceValid state steps) :
    (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition^[
        steps.length])
        (D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState state) =
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState
        (tribonacciApplyStepsCode state steps) := by
  induction steps generalizing state with
  | nil => rfl
  | cons step rest ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        tribonacci_decode_step hvalid.2.1]
      exact ih hvalid.2.2

structure TribonacciCodedOrbit where
  start : CodedState
  steps : List Step
  lowState : CodedState
  deriving DecidableEq

def tribonacciOrbitStates (orbit : TribonacciCodedOrbit) : List CodedState :=
  tribonacciTraceCode orbit.start orbit.steps

noncomputable def tribonacciDecodedOrbitStates
    (orbit : TribonacciCodedOrbit) : List PeriodicState :=
  (tribonacciOrbitStates orbit).map
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.decodeTribonacciState

def tribonacciCodedOrbitValid (orbit : TribonacciCodedOrbit) : Prop :=
  tribonacciCodedTraceValid orbit.start orbit.steps ∧
    tribonacciApplyStepsCode orbit.start orbit.steps = orbit.start

def tribonacciMakeOrbit (kind : Gap) (steps lowPrefix : List Step) :
    TribonacciCodedOrbit :=
  let start : CodedState :=
    ⟨kind,
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathCandidateCode
        steps⟩
  ⟨start, steps, tribonacciApplyStepsCode start lowPrefix⟩

def tribonacciChampionPeriodicOrbit : TribonacciCodedOrbit :=
  tribonacciMakeOrbit .large [.largeRight, .combinedLeft] []

def tribonacciPeriodicOrbitRepresentativesFive : List TribonacciCodedOrbit :=
  [tribonacciMakeOrbit .large [.largeLeft] [],
   tribonacciChampionPeriodicOrbit,
   tribonacciMakeOrbit .small [.smallThrough, .largeRight, .combinedRight] [],
   tribonacciMakeOrbit .combined [.combinedLeft, .largeLeft, .largeRight] [],
   tribonacciMakeOrbit .small
      [.smallThrough, .largeLeft, .largeRight, .combinedRight]
      [.smallThrough, .largeLeft],
   tribonacciMakeOrbit .combined
      [.combinedLeft, .largeLeft, .largeLeft, .largeRight] [],
   tribonacciMakeOrbit .small
      [.smallThrough, .largeLeft, .largeLeft, .largeRight, .combinedRight]
      [.smallThrough, .largeLeft, .largeLeft],
   tribonacciMakeOrbit .small
      [.smallThrough, .largeRight, .combinedLeft, .largeRight, .combinedRight]
      [.smallThrough, .largeRight, .combinedLeft],
   tribonacciMakeOrbit .combined
      [.combinedLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight] [],
   tribonacciMakeOrbit .combined
      [.combinedLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight] []]

/-- The representative lengths give one period-one orbit, one period-two,
two each of periods three and four, and four of period five. -/
theorem tribonacci_periodic_orbit_period_distribution_five :
    tribonacciPeriodicOrbitRepresentativesFive.map (fun orbit => orbit.steps.length) =
      [1, 2, 3, 3, 4, 4, 5, 5, 5, 5] := by
  norm_num [tribonacciPeriodicOrbitRepresentativesFive,
    tribonacciChampionPeriodicOrbit, tribonacciMakeOrbit]

theorem tribonacci_inverse_polynomial : t⁻¹ = t ^ 2 - t - 1 := by
  have htne : t ≠ 0 :=
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_ne_zero
  rw [inv_eq_one_div]
  apply (div_eq_iff htne).2
  nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic]

set_option maxHeartbeats 1000000 in
-- Exact cubic inequalities for all ten representatives need the larger budget.
/-- All ten exact coded cycles close, use their certified branches, and remain
inside the appropriate normalized gap. -/
theorem tribonacci_periodic_orbit_representatives_valid :
    tribonacciPeriodicOrbitRepresentativesFive.Forall tribonacciCodedOrbitValid := by
  norm_num [tribonacciPeriodicOrbitRepresentativesFive,
    tribonacciChampionPeriodicOrbit, tribonacciMakeOrbit,
    tribonacciCodedOrbitValid, tribonacciCodedTraceValid,
    tribonacciCodedStateInGap, tribonacciCodedStepValid,
    tribonacciApplyStepsCode, tribonacciApplyStepCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathCandidateCode,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPathAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciAffineCompose,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciIdentityAffine,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepSource,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciStepTarget,
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeValue,
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
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciCodeRoot,
    tribonacci_inverse_polynomial]
  repeat' apply And.intro
  all_goals try rw [abs_of_pos
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos] at *
  all_goals nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic,
    D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant,
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two]

/-- Each displayed cycle closes and has no repeated coded state before closing. -/
theorem tribonacci_periodic_orbit_codes_close_and_are_nodup :
    tribonacciPeriodicOrbitRepresentativesFive.Forall fun orbit =>
      tribonacciApplyStepsCode orbit.start orbit.steps = orbit.start ∧
        (tribonacciOrbitStates orbit).Nodup := by
  norm_num [tribonacciPeriodicOrbitRepresentativesFive,
    tribonacciChampionPeriodicOrbit, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepsCode, tribonacciApplyStepCode,
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

def tribonacciEnumeratedOrbitStatesFive : Finset CodedState :=
  (tribonacciPeriodicOrbitRepresentativesFive.flatMap tribonacciOrbitStates).toFinset

theorem tribonacci_periodic_orbit_state_codes_nodup :
    (tribonacciPeriodicOrbitRepresentativesFive.flatMap tribonacciOrbitStates).Nodup := by
  norm_num [tribonacciPeriodicOrbitRepresentativesFive,
    tribonacciChampionPeriodicOrbit, tribonacciMakeOrbit,
    tribonacciOrbitStates, tribonacciTraceCode,
    tribonacciApplyStepsCode, tribonacciApplyStepCode,
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

end D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
