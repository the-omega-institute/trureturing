/- GID: D5/S0/Tower/Champions/GoldenPeriodicEnumeration
   generality: I
   mirror-B: D5/B/S0/Tower/Champions/GoldenPeriodicEnumeration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete period-at-most-seven enumeration for the golden survivor map. -/

import D5.S0.Tower.Champions.GoldenSurvivorTubes

namespace D5.S0.Tower.Champions.GoldenPeriodicEnumeration

open D5.S0.Tower.Champions.GoldenSurvivorTubes

local notation "φ" => Real.goldenRatio

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen golden transition, survivor arm, exact
     champion cycle, and global survivor classification, but no finite-period
     enumeration or completeness theorem.
   * Pinned mathlib supplies finite lists, rational arithmetic, function
     iteration, and golden-ratio irrationality. No theorem specializes these
     tools to the weighted two-chart golden transition.
   * The certificate below therefore enumerates every closed symbolic itinerary,
     solves its affine fixed-point equation over Q(phi), and proves that the
     resulting twelve disjoint cycles exhaust every real periodic state through
     period seven. -/

/-- An exact code `(a,b)` denotes the real number `a + b * phi`. -/
abbrev GoldenQuadraticCode := ℚ × ℚ

def goldenCodeZero : GoldenQuadraticCode := (0, 0)

def goldenCodeOne : GoldenQuadraticCode := (1, 0)

def goldenCodePhi : GoldenQuadraticCode := (0, 1)

def goldenCodeAdd (x y : GoldenQuadraticCode) : GoldenQuadraticCode :=
  (x.1 + y.1, x.2 + y.2)

def goldenCodeNeg (x : GoldenQuadraticCode) : GoldenQuadraticCode :=
  (-x.1, -x.2)

def goldenCodeSub (x y : GoldenQuadraticCode) : GoldenQuadraticCode :=
  goldenCodeAdd x (goldenCodeNeg y)

/-- Multiplication reduced by `phi^2 = phi + 1`. -/
def goldenCodeMul (x y : GoldenQuadraticCode) : GoldenQuadraticCode :=
  (x.1 * y.1 + x.2 * y.2,
    x.1 * y.2 + x.2 * y.1 + x.2 * y.2)

def goldenCodeNorm (x : GoldenQuadraticCode) : ℚ :=
  x.1 * (x.1 + x.2) - x.2 ^ 2

/-- Inversion in `Q(phi)`, with the field convention that zero maps to zero. -/
def goldenCodeInv (x : GoldenQuadraticCode) : GoldenQuadraticCode :=
  ((x.1 + x.2) / goldenCodeNorm x, -x.2 / goldenCodeNorm x)

def goldenCodeDiv (x y : GoldenQuadraticCode) : GoldenQuadraticCode :=
  goldenCodeMul x (goldenCodeInv y)

noncomputable def goldenCodeValue (x : GoldenQuadraticCode) : Real :=
  (x.1 : Real) + (x.2 : Real) * φ

theorem golden_code_value_add (x y : GoldenQuadraticCode) :
    goldenCodeValue (goldenCodeAdd x y) = goldenCodeValue x + goldenCodeValue y := by
  simp [goldenCodeValue, goldenCodeAdd]
  ring

theorem golden_code_value_neg (x : GoldenQuadraticCode) :
    goldenCodeValue (goldenCodeNeg x) = -goldenCodeValue x := by
  simp [goldenCodeValue, goldenCodeNeg]
  ring

theorem golden_code_value_sub (x y : GoldenQuadraticCode) :
    goldenCodeValue (goldenCodeSub x y) = goldenCodeValue x - goldenCodeValue y := by
  rw [goldenCodeSub, golden_code_value_add, golden_code_value_neg]
  ring

theorem golden_code_value_mul (x y : GoldenQuadraticCode) :
    goldenCodeValue (goldenCodeMul x y) = goldenCodeValue x * goldenCodeValue y := by
  simp only [goldenCodeValue, goldenCodeMul]
  push_cast
  calc
    (x.1 : Real) * y.1 + x.2 * y.2 +
          ((x.1 : Real) * y.2 + x.2 * y.1 + x.2 * y.2) * φ =
        (x.1 : Real) * y.1 + ((x.1 : Real) * y.2 + x.2 * y.1) * φ +
          x.2 * y.2 * (φ + 1) := by ring
    _ = (x.1 : Real) * y.1 + ((x.1 : Real) * y.2 + x.2 * y.1) * φ +
          x.2 * y.2 * φ ^ 2 := by rw [Real.goldenRatio_sq]
    _ = ((x.1 : Real) + x.2 * φ) * ((y.1 : Real) + y.2 * φ) := by ring

theorem golden_code_mul_inv (x : GoldenQuadraticCode) (hnorm : goldenCodeNorm x ≠ 0) :
    goldenCodeMul x (goldenCodeInv x) = goldenCodeOne := by
  apply Prod.ext
  · change x.1 * ((x.1 + x.2) / goldenCodeNorm x) +
        x.2 * (-x.2 / goldenCodeNorm x) = 1
    field_simp [hnorm]
    simp only [goldenCodeNorm]
    ring
  · change x.1 * (-x.2 / goldenCodeNorm x) +
          x.2 * ((x.1 + x.2) / goldenCodeNorm x) +
        x.2 * (-x.2 / goldenCodeNorm x) = 0
    field_simp [hnorm]
    simp only [goldenCodeNorm]
    ring

theorem golden_code_value_inv (x : GoldenQuadraticCode) (hnorm : goldenCodeNorm x ≠ 0) :
    goldenCodeValue (goldenCodeInv x) = (goldenCodeValue x)⁻¹ := by
  have hproduct : goldenCodeValue x * goldenCodeValue (goldenCodeInv x) = 1 := by
    rw [← golden_code_value_mul, golden_code_mul_inv x hnorm]
    norm_num [goldenCodeValue, goldenCodeOne]
  exact eq_inv_of_mul_eq_one_right hproduct

theorem golden_code_value_div (x y : GoldenQuadraticCode) (hnorm : goldenCodeNorm y ≠ 0) :
    goldenCodeValue (goldenCodeDiv x y) = goldenCodeValue x / goldenCodeValue y := by
  rw [goldenCodeDiv, golden_code_value_mul, golden_code_value_inv y hnorm, div_eq_mul_inv]

theorem golden_code_value_ne_zero_of_norm_ne_zero (x : GoldenQuadraticCode)
    (hnorm : goldenCodeNorm x ≠ 0) : goldenCodeValue x ≠ 0 := by
  intro hzero
  have hproduct : goldenCodeValue x * goldenCodeValue (goldenCodeInv x) = 1 := by
    rw [← golden_code_value_mul, golden_code_mul_inv x hnorm]
    norm_num [goldenCodeValue, goldenCodeOne]
  rw [hzero, zero_mul] at hproduct
  norm_num at hproduct

theorem golden_code_value_injective : Function.Injective goldenCodeValue := by
  intro x y hvalue
  by_cases hsecond : x.2 = y.2
  · have hfirstReal : (x.1 : Real) = (y.1 : Real) := by
      rw [goldenCodeValue, goldenCodeValue, hsecond] at hvalue
      linarith
    have hfirst : x.1 = y.1 := by exact_mod_cast hfirstReal
    exact Prod.ext hfirst hsecond
  · exfalso
    have hdiff : x.2 - y.2 ≠ 0 := sub_ne_zero.mpr hsecond
    apply Real.goldenRatio_irrational
    refine ⟨-(x.1 - y.1) / (x.2 - y.2), ?_⟩
    push_cast
    apply (div_eq_iff (by exact_mod_cast hdiff)).2
    rw [goldenCodeValue, goldenCodeValue] at hvalue
    nlinarith

/-- The three branch letters of the two-chart golden transition. -/
inductive GoldenPeriodicStep where
  | left
  | right
  | through
  deriving DecidableEq, Repr

def goldenStepSource : GoldenPeriodicStep → GoldenGapKind
  | .left | .right => .large
  | .through => .small

def goldenStepTarget : GoldenPeriodicStep → GoldenGapKind
  | .left | .through => .large
  | .right => .small

structure GoldenAffineCode where
  multiplier : GoldenQuadraticCode
  offset : GoldenQuadraticCode
  deriving DecidableEq

def goldenIdentityAffine : GoldenAffineCode :=
  ⟨goldenCodeOne, goldenCodeZero⟩

def goldenStepAffine : GoldenPeriodicStep → GoldenAffineCode
  | .left => ⟨goldenCodePhi, goldenCodeZero⟩
  | .right => ⟨goldenCodeAdd goldenCodeOne goldenCodePhi, goldenCodeNeg goldenCodePhi⟩
  | .through => goldenIdentityAffine

noncomputable def goldenStepCoordinate (step : GoldenPeriodicStep) (u : Real) : Real :=
  match step with
  | .left => φ * u
  | .right => φ ^ 2 * u - φ
  | .through => u

theorem golden_step_affine_value (step : GoldenPeriodicStep) (u : Real) :
    goldenCodeValue (goldenStepAffine step).multiplier * u +
        goldenCodeValue (goldenStepAffine step).offset = goldenStepCoordinate step u := by
  cases step
  · simp [goldenStepAffine, goldenCodeValue, goldenCodePhi, goldenCodeZero,
      goldenStepCoordinate]
  · simp only [goldenStepAffine, goldenCodeValue, goldenCodeAdd, goldenCodeOne,
      goldenCodePhi, goldenCodeNeg]
    norm_num
    change (1 + φ) * u - φ = φ ^ 2 * u - φ
    rw [Real.goldenRatio_sq]
    ring
  · simp [goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeOne,
      goldenCodeZero, goldenStepCoordinate]

/-- `outer` after `inner`. -/
def goldenAffineCompose (outer inner : GoldenAffineCode) : GoldenAffineCode :=
  ⟨goldenCodeMul outer.multiplier inner.multiplier,
    goldenCodeAdd (goldenCodeMul outer.multiplier inner.offset) outer.offset⟩

def goldenPathAffine (steps : List GoldenPeriodicStep) : GoldenAffineCode :=
  steps.foldl (fun affine step => goldenAffineCompose (goldenStepAffine step) affine)
    goldenIdentityAffine

noncomputable def goldenPathCoordinate (steps : List GoldenPeriodicStep) (u : Real) : Real :=
  steps.foldl (fun coordinate step => goldenStepCoordinate step coordinate) u

theorem golden_path_affine_value_aux (steps : List GoldenPeriodicStep)
    (affine : GoldenAffineCode) (u : Real) :
    goldenCodeValue
          (steps.foldl
            (fun current step => goldenAffineCompose (goldenStepAffine step) current)
            affine).multiplier * u +
        goldenCodeValue
          (steps.foldl
            (fun current step => goldenAffineCompose (goldenStepAffine step) current)
            affine).offset =
      goldenPathCoordinate steps
        (goldenCodeValue affine.multiplier * u + goldenCodeValue affine.offset) := by
  induction steps generalizing affine with
  | nil => rfl
  | cons step rest ih =>
      simp only [List.foldl_cons, goldenPathCoordinate]
      rw [ih]
      simp only [goldenAffineCompose, golden_code_value_mul, golden_code_value_add]
      change goldenPathCoordinate rest _ = goldenPathCoordinate rest _
      apply congrArg (goldenPathCoordinate rest)
      rw [← golden_step_affine_value step
        (goldenCodeValue affine.multiplier * u + goldenCodeValue affine.offset)]
      ring

theorem golden_path_affine_value (steps : List GoldenPeriodicStep) (u : Real) :
    goldenCodeValue (goldenPathAffine steps).multiplier * u +
        goldenCodeValue (goldenPathAffine steps).offset = goldenPathCoordinate steps u := by
  rw [goldenPathAffine, golden_path_affine_value_aux]
  norm_num [goldenIdentityAffine, goldenCodeValue, goldenCodeOne, goldenCodeZero]

def goldenPathCandidateCode (steps : List GoldenPeriodicStep) : GoldenQuadraticCode :=
  goldenCodeDiv (goldenPathAffine steps).offset
    (goldenCodeSub goldenCodeOne (goldenPathAffine steps).multiplier)

/-- All symbolic paths of exactly `period` transitions from a specified chart. -/
def goldenPathsFrom : GoldenGapKind → Nat → List (List GoldenPeriodicStep × GoldenGapKind)
  | kind, 0 => [([], kind)]
  | .large, period + 1 =>
      (goldenPathsFrom .large period).map (fun path => (.left :: path.1, path.2)) ++
        (goldenPathsFrom .small period).map (fun path => (.right :: path.1, path.2))
  | .small, period + 1 =>
      (goldenPathsFrom .large period).map (fun path => (.through :: path.1, path.2))

/-- Every chart-compatible closed itinerary of exactly the requested period. -/
def goldenClosedItineraries (period : Nat) : List (GoldenGapKind × List GoldenPeriodicStep) :=
  ((goldenPathsFrom .large period).filterMap fun path =>
        if path.2 = .large then some (.large, path.1) else none) ++
    ((goldenPathsFrom .small period).filterMap fun path =>
      if path.2 = .small then some (.small, path.1) else none)

/-- The branch word read from an actual real orbit segment. -/
noncomputable def goldenActualSteps : Nat → GoldenSurvivorState → List GoldenPeriodicStep
  | 0, _ => []
  | period + 1, state =>
      match state.kind with
      | .large =>
          if state.coordinate ≤ goldenInverse then
            .left :: goldenActualSteps period (goldenTransition state)
          else
            .right :: goldenActualSteps period (goldenTransition state)
      | .small => .through :: goldenActualSteps period (goldenTransition state)

theorem golden_actual_steps_length (period : Nat) (state : GoldenSurvivorState) :
    (goldenActualSteps period state).length = period := by
  induction period generalizing state with
  | zero => rfl
  | succ period ih =>
      cases state with
      | mk kind coordinate =>
          cases kind <;> simp only [goldenActualSteps, List.length_cons]
          · split <;> simp [ih]
          · simp [ih]

theorem golden_actual_steps_mem_paths (period : Nat) (state : GoldenSurvivorState) :
    (goldenActualSteps period state, ((goldenTransition^[period]) state).kind) ∈
      goldenPathsFrom state.kind period := by
  induction period generalizing state with
  | zero => simp [goldenActualSteps, goldenPathsFrom]
  | succ period ih =>
      rw [Function.iterate_succ_apply]
      cases state with
      | mk kind coordinate =>
          cases kind
          · simp only [goldenActualSteps, goldenPathsFrom, List.mem_append,
              List.mem_map, goldenTransition]
            split_ifs with hbranch
            · left
              exact ⟨(goldenActualSteps period
                  ⟨.large, φ * coordinate⟩,
                ((goldenTransition^[period]) ⟨.large, φ * coordinate⟩).kind),
                ih ⟨.large, φ * coordinate⟩, rfl⟩
            · right
              exact ⟨(goldenActualSteps period
                  ⟨.small, φ ^ 2 * coordinate - φ⟩,
                ((goldenTransition^[period])
                  ⟨.small, φ ^ 2 * coordinate - φ⟩).kind),
                ih ⟨.small, φ ^ 2 * coordinate - φ⟩, rfl⟩
          · simp only [goldenActualSteps, goldenPathsFrom, List.mem_map, goldenTransition]
            exact ⟨(goldenActualSteps period ⟨.large, coordinate⟩,
              ((goldenTransition^[period]) ⟨.large, coordinate⟩).kind),
              ih ⟨.large, coordinate⟩, rfl⟩

theorem golden_actual_steps_coordinate (period : Nat) (state : GoldenSurvivorState) :
    goldenPathCoordinate (goldenActualSteps period state) state.coordinate =
      ((goldenTransition^[period]) state).coordinate := by
  induction period generalizing state with
  | zero => rfl
  | succ period ih =>
      rw [Function.iterate_succ_apply]
      cases state with
      | mk kind coordinate =>
          cases kind
          · simp only [goldenActualSteps, goldenPathCoordinate, goldenTransition]
            split_ifs with hbranch
            · change goldenPathCoordinate
                (goldenActualSteps period
                  (⟨.large, φ * coordinate⟩ : GoldenSurvivorState))
                  (φ * coordinate) = _
              exact ih (⟨.large, φ * coordinate⟩ : GoldenSurvivorState)
            · change goldenPathCoordinate
                (goldenActualSteps period
                  (⟨.small, φ ^ 2 * coordinate - φ⟩ : GoldenSurvivorState))
                  (φ ^ 2 * coordinate - φ) = _
              exact ih (⟨.small, φ ^ 2 * coordinate - φ⟩ : GoldenSurvivorState)
          · simp only [goldenActualSteps, goldenPathCoordinate, List.foldl_cons,
              goldenTransition]
            change goldenPathCoordinate
              (goldenActualSteps period
                (⟨.large, coordinate⟩ : GoldenSurvivorState)) coordinate = _
            exact ih (⟨.large, coordinate⟩ : GoldenSurvivorState)

structure GoldenCodedState where
  kind : GoldenGapKind
  coordinate : GoldenQuadraticCode
  deriving DecidableEq

noncomputable def decodeGoldenState (state : GoldenCodedState) : GoldenSurvivorState :=
  ⟨state.kind, goldenCodeValue state.coordinate⟩

def goldenFixedPointCodes (period : Nat) : List GoldenCodedState :=
  (goldenClosedItineraries period).map fun itinerary =>
    ⟨itinerary.1, goldenPathCandidateCode itinerary.2⟩

/-- All distinct periodic-point codes found at periods one through seven. -/
def goldenPeriodicPointCodesSeven : Finset GoldenCodedState :=
  ((List.range 7).flatMap fun period => goldenFixedPointCodes (period + 1)).toFinset

def goldenClosedItinerariesSeven : List (GoldenGapKind × List GoldenPeriodicStep) :=
  (List.range 7).flatMap fun period => goldenClosedItineraries (period + 1)

/-- Every enumerated affine equation has a nonzero denominator. -/
theorem golden_closed_itinerary_denominators_seven :
    goldenClosedItinerariesSeven.Forall fun itinerary =>
      goldenCodeNorm
        (goldenCodeSub goldenCodeOne (goldenPathAffine itinerary.2).multiplier) ≠ 0 := by
  set_option maxRecDepth 100000 in
    have hrange : List.range 7 = [0, 1, 2, 3, 4, 5, 6] := by decide
    rw [goldenClosedItinerariesSeven, hrange]
    simp [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_cons, List.map_nil, List.filterMap_nil,
      goldenClosedItineraries, goldenPathsFrom]
    norm_num [goldenPathAffine, goldenAffineCompose, goldenStepAffine,
      goldenIdentityAffine, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
      goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi]

theorem golden_actual_steps_mem_closed {period : Nat} {state : GoldenSurvivorState}
    (hperiod : (goldenTransition^[period]) state = state) :
    (state.kind, goldenActualSteps period state) ∈ goldenClosedItineraries period := by
  have hpaths := golden_actual_steps_mem_paths period state
  have hkind : ((goldenTransition^[period]) state).kind = state.kind :=
    congrArg GoldenSurvivorState.kind hperiod
  have hfilter :
      (state.kind, goldenActualSteps period state) ∈
        (goldenPathsFrom state.kind period).filterMap fun path =>
          if path.2 = state.kind then some (state.kind, path.1) else none := by
    simp only [List.mem_filterMap]
    exact ⟨(goldenActualSteps period state,
      ((goldenTransition^[period]) state).kind), hpaths, by simp [hkind]⟩
  rw [goldenClosedItineraries, List.mem_append]
  cases hstateKind : state.kind
  · left
    simpa only [hstateKind] using hfilter
  · right
    simpa only [hstateKind] using hfilter

/-- Completeness of the finite point enumeration: every nonzero period at most
seven is one of the sixty decoded exact quadratic points. -/
theorem golden_periodic_point_enumeration_complete {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 7)
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[period]) state = state) :
    ∃ code ∈ goldenPeriodicPointCodesSeven, state = decodeGoldenState code := by
  obtain ⟨index, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hperiodPos)
  have hindex : index < 7 := by omega
  let steps := goldenActualSteps (index + 1) state
  have hitinerary : (state.kind, steps) ∈ goldenClosedItineraries (index + 1) := by
    exact golden_actual_steps_mem_closed hperiod
  have hitinerarySeven : (state.kind, steps) ∈ goldenClosedItinerariesSeven := by
    simp only [goldenClosedItinerariesSeven, List.mem_flatMap]
    exact ⟨index, List.mem_range.mpr hindex, hitinerary⟩
  have hnorm : goldenCodeNorm
      (goldenCodeSub goldenCodeOne (goldenPathAffine steps).multiplier) ≠ 0 :=
    List.forall_iff_forall_mem.mp golden_closed_itinerary_denominators_seven
      (state.kind, steps) hitinerarySeven
  have hclosedCoordinate : goldenPathCoordinate steps state.coordinate = state.coordinate := by
    calc
      goldenPathCoordinate steps state.coordinate =
          ((goldenTransition^[index + 1]) state).coordinate :=
        golden_actual_steps_coordinate (index + 1) state
      _ = state.coordinate := congrArg GoldenSurvivorState.coordinate hperiod
  have haffine := golden_path_affine_value steps state.coordinate
  rw [hclosedCoordinate] at haffine
  have hdenValue :
      goldenCodeValue
        (goldenCodeSub goldenCodeOne (goldenPathAffine steps).multiplier) ≠ 0 :=
    golden_code_value_ne_zero_of_norm_ne_zero _ hnorm
  have hcandidate :
      goldenCodeValue (goldenPathCandidateCode steps) = state.coordinate := by
    rw [goldenPathCandidateCode, golden_code_value_div _ _ hnorm]
    apply (div_eq_iff hdenValue).2
    rw [golden_code_value_sub]
    have hone : goldenCodeValue goldenCodeOne = 1 := by
      norm_num [goldenCodeValue, goldenCodeOne]
    rw [hone]
    linear_combination haffine
  let code : GoldenCodedState :=
    ⟨state.kind, goldenPathCandidateCode steps⟩
  have hcode : code ∈ goldenPeriodicPointCodesSeven := by
    rw [goldenPeriodicPointCodesSeven, List.mem_toFinset]
    simp only [List.mem_flatMap]
    refine ⟨index, List.mem_range.mpr hindex, ?_⟩
    simp only [goldenFixedPointCodes, List.mem_map]
    exact ⟨(state.kind, steps), hitinerary, rfl⟩
  refine ⟨code, hcode, ?_⟩
  cases state with
  | mk kind coordinate =>
      simp only [code, decodeGoldenState]
      rw [hcandidate]

/-- The exact-period fixed-point counts before points of smaller period are deduplicated. -/
theorem golden_fixed_point_counts_through_seven :
    (List.range 7).map (fun period => (goldenFixedPointCodes (period + 1)).length) =
      [1, 3, 4, 7, 11, 18, 29] := by
  set_option maxRecDepth 100000 in
    decide

def goldenApplyStepCode (state : GoldenCodedState)
    (step : GoldenPeriodicStep) : GoldenCodedState :=
  let affine := goldenStepAffine step
  ⟨goldenStepTarget step,
    goldenCodeAdd (goldenCodeMul affine.multiplier state.coordinate) affine.offset⟩

def goldenApplyStepsCode : GoldenCodedState → List GoldenPeriodicStep → GoldenCodedState
  | state, [] => state
  | state, step :: rest => goldenApplyStepsCode (goldenApplyStepCode state step) rest

def goldenCodedStepValid (state : GoldenCodedState) (step : GoldenPeriodicStep) : Prop :=
  state.kind = goldenStepSource step ∧
    match step with
    | .left => goldenCodeValue state.coordinate ≤ goldenInverse
    | .right => goldenInverse < goldenCodeValue state.coordinate
    | .through => True

def goldenCodedStateInUnit (state : GoldenCodedState) : Prop :=
  0 ≤ goldenCodeValue state.coordinate ∧ goldenCodeValue state.coordinate ≤ 1

def goldenCodedTraceValid : GoldenCodedState → List GoldenPeriodicStep → Prop
  | _, [] => True
  | state, step :: rest =>
      goldenCodedStateInUnit state ∧ goldenCodedStepValid state step ∧
        goldenCodedTraceValid (goldenApplyStepCode state step) rest

theorem golden_decode_step {state : GoldenCodedState} {step : GoldenPeriodicStep}
    (hvalid : goldenCodedStepValid state step) :
    goldenTransition (decodeGoldenState state) =
      decodeGoldenState (goldenApplyStepCode state step) := by
  rcases state with ⟨kind, coordinate⟩
  cases step
  · rcases hvalid with ⟨hkind, hbranch⟩
    simp only [goldenStepSource] at hkind
    change goldenCodeValue coordinate ≤ goldenInverse at hbranch
    subst kind
    simp only [decodeGoldenState]
    rw [goldenTransition]
    rw [if_pos hbranch]
    simp only [goldenApplyStepCode, goldenStepTarget, goldenStepAffine]
    congr 1
    rw [golden_code_value_add, golden_code_value_mul]
    norm_num [goldenCodeValue, goldenCodePhi, goldenCodeZero]
  · rcases hvalid with ⟨hkind, hbranch⟩
    simp only [goldenStepSource] at hkind
    change goldenInverse < goldenCodeValue coordinate at hbranch
    subst kind
    simp only [decodeGoldenState]
    rw [goldenTransition]
    rw [if_neg (not_le.mpr hbranch)]
    simp only [goldenApplyStepCode, goldenStepTarget, goldenStepAffine]
    congr 1
    rw [golden_code_value_add, golden_code_value_mul, golden_code_value_add,
      golden_code_value_neg]
    norm_num [goldenCodeValue, goldenCodeOne, goldenCodePhi]
    ring_nf
  · rcases hvalid with ⟨hkind, _⟩
    simp only [goldenStepSource] at hkind
    subst kind
    simp only [decodeGoldenState, goldenTransition, goldenApplyStepCode,
      goldenStepTarget, goldenStepAffine, goldenIdentityAffine]
    congr 1
    rw [golden_code_value_add, golden_code_value_mul]
    norm_num [goldenCodeValue, goldenCodeOne, goldenCodeZero]

theorem golden_decode_steps {state : GoldenCodedState} {steps : List GoldenPeriodicStep}
    (hvalid : goldenCodedTraceValid state steps) :
    (goldenTransition^[steps.length]) (decodeGoldenState state) =
      decodeGoldenState (goldenApplyStepsCode state steps) := by
  induction steps generalizing state with
  | nil => rfl
  | cons step rest ih =>
      rcases hvalid with ⟨_, hstep, hrest⟩
      rw [List.length_cons, Function.iterate_succ_apply, golden_decode_step hstep]
      exact ih hrest

def goldenTraceCode : GoldenCodedState → List GoldenPeriodicStep → List GoldenCodedState
  | _, [] => []
  | state, step :: rest =>
      state :: goldenTraceCode (goldenApplyStepCode state step) rest

structure GoldenCodedOrbit where
  start : GoldenCodedState
  steps : List GoldenPeriodicStep
  lowState : GoldenCodedState
  deriving DecidableEq

def goldenOrbitStates (orbit : GoldenCodedOrbit) : List GoldenCodedState :=
  goldenTraceCode orbit.start orbit.steps

def goldenCodedOrbitValid (orbit : GoldenCodedOrbit) : Prop :=
  goldenCodedTraceValid orbit.start orbit.steps ∧
    goldenApplyStepsCode orbit.start orbit.steps = orbit.start

def qphi (a b : ℚ) : GoldenQuadraticCode := (a, b)

def goldenChampionPeriodicOrbit : GoldenCodedOrbit :=
  ⟨⟨.large, qphi (1 / 2) 0⟩,
    [.left, .right, .through],
    ⟨.large, qphi 0 (1 / 2)⟩⟩

def goldenPeriodicOrbitRepresentativesSeven : List GoldenCodedOrbit :=
  [⟨⟨.large, qphi 0 0⟩, [.left], ⟨.large, qphi 0 0⟩⟩,
   ⟨⟨.large, qphi 1 0⟩, [.right, .through], ⟨.large, qphi 1 0⟩⟩,
   goldenChampionPeriodicOrbit,
   ⟨⟨.large, qphi (3 / 5) (-1 / 5)⟩, [.left, .left, .right, .through],
      ⟨.small, qphi (3 / 5) (-1 / 5)⟩⟩,
   ⟨⟨.large, qphi (5 / 11) (-2 / 11)⟩,
      [.left, .left, .left, .right, .through],
      ⟨.small, qphi (5 / 11) (-2 / 11)⟩⟩,
   ⟨⟨.large, qphi (8 / 11) (-1 / 11)⟩,
      [.left, .right, .through, .right, .through],
      ⟨.large, qphi (-1 / 11) (7 / 11)⟩⟩,
   ⟨⟨.large, qphi (1 / 2) (-1 / 4)⟩,
      [.left, .left, .left, .left, .right, .through],
      ⟨.small, qphi (1 / 2) (-1 / 4)⟩⟩,
   ⟨⟨.large, qphi (3 / 4) (-1 / 4)⟩,
      [.left, .left, .right, .through, .right, .through],
      ⟨.large, qphi (1 / 2) (1 / 4)⟩⟩,
   ⟨⟨.large, qphi (13 / 29) (-7 / 29)⟩,
      [.left, .left, .left, .left, .left, .right, .through],
      ⟨.small, qphi (13 / 29) (-7 / 29)⟩⟩,
   ⟨⟨.large, qphi (19 / 29) (-8 / 29)⟩,
      [.left, .left, .left, .right, .through, .right, .through],
      ⟨.large, qphi (3 / 29) (14 / 29)⟩⟩,
   ⟨⟨.large, qphi (12 / 29) (-2 / 29)⟩,
      [.left, .left, .right, .through, .left, .right, .through],
      ⟨.small, qphi (12 / 29) (-2 / 29)⟩⟩,
   ⟨⟨.large, qphi (24 / 29) (-4 / 29)⟩,
      [.left, .right, .through, .right, .through, .right, .through],
      ⟨.large, qphi (-4 / 29) (20 / 29)⟩⟩]

theorem golden_periodic_orbit_codes_close_and_are_nodup :
    goldenPeriodicOrbitRepresentativesSeven.Forall fun orbit =>
      goldenApplyStepsCode orbit.start orbit.steps = orbit.start ∧
        (goldenOrbitStates orbit).Nodup := by
  norm_num [goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget,
    goldenOrbitStates, goldenTraceCode, goldenCodeAdd, goldenCodeMul,
    goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

theorem golden_periodic_orbit_low_states_mem :
    goldenPeriodicOrbitRepresentativesSeven.Forall fun orbit =>
      orbit.lowState ∈ goldenOrbitStates orbit := by
  norm_num [goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
    goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]

set_option maxHeartbeats 1000000 in
-- The explicit twelve-cycle real-inequality normalization exceeds the default budget.
/-- Every displayed code follows the correct branch inequalities and stays in
the closed unit chart. -/
theorem golden_periodic_orbit_representatives_valid :
    goldenPeriodicOrbitRepresentativesSeven.Forall goldenCodedOrbitValid := by
  have hphiLower : (1 : Real) < φ := Real.one_lt_goldenRatio
  have hphiUpper : φ < 2 := Real.goldenRatio_lt_two
  have hphiRadical : φ = (1 + Real.sqrt 5) / 2 := rfl
  norm_num [goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenCodedOrbitValid,
    goldenCodedTraceValid, goldenCodedStateInUnit, goldenCodedStepValid,
    goldenApplyStepsCode, goldenApplyStepCode, goldenStepSource, goldenStepTarget,
    goldenStepAffine, goldenIdentityAffine, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, goldenCodeNeg,
    goldenOrbitStates, goldenTraceCode, qphi, golden_inverse_eq_sub_one]
  repeat' apply And.intro
  all_goals nlinarith [Real.goldenRatio_sq, hphiLower, hphiUpper, hphiRadical]

def goldenEnumeratedOrbitStatesSeven : Finset GoldenCodedState :=
  (goldenPeriodicOrbitRepresentativesSeven.flatMap goldenOrbitStates).toFinset

/-- The twelve cycle lists are pairwise disjoint as well as internally duplicate-free. -/
theorem golden_periodic_orbit_state_codes_nodup :
    (goldenPeriodicOrbitRepresentativesSeven.flatMap goldenOrbitStates).Nodup := by
  norm_num [goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenIdentityAffine, goldenStepTarget, goldenCodeAdd, goldenCodeMul, goldenCodePhi,
    goldenCodeZero, goldenCodeOne, goldenCodeNeg, qphi]
  decide

set_option maxHeartbeats 1000000 in
/-- The symbolic fixed-point generator and the twelve explicit cycles give the same set. -/
theorem golden_enumerated_orbit_states_eq_fixed_points :
    goldenEnumeratedOrbitStatesSeven = goldenPeriodicPointCodesSeven := by
  apply Finset.ext
  intro code
  rw [goldenEnumeratedOrbitStatesSeven, goldenPeriodicPointCodesSeven]
  simp only [List.mem_toFinset]
  simp [List.range_succ, goldenPeriodicOrbitRepresentativesSeven,
    goldenChampionPeriodicOrbit, goldenOrbitStates, goldenTraceCode,
    goldenFixedPointCodes, goldenClosedItineraries, goldenPathsFrom]
  norm_num [goldenApplyStepCode, goldenStepAffine, goldenIdentityAffine,
    goldenStepTarget, goldenPathCandidateCode, goldenPathAffine, goldenAffineCompose,
    goldenCodeDiv, goldenCodeInv, goldenCodeNorm, goldenCodeSub, goldenCodeNeg,
    goldenCodeAdd, goldenCodeMul, goldenCodeOne, goldenCodeZero, goldenCodePhi, qphi]
  aesop

/-- Deduplication of all fixed-point equations through period seven gives sixty states. -/
theorem golden_periodic_point_code_count_seven :
    goldenPeriodicPointCodesSeven.card = 60 := by
  rw [← golden_enumerated_orbit_states_eq_fixed_points, goldenEnumeratedOrbitStatesSeven,
    List.toFinset_card_of_nodup golden_periodic_orbit_state_codes_nodup]
  norm_num [goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenOrbitStates, goldenTraceCode]

/-- The sixty distinct states partition into twelve displayed periodic cycles. -/
theorem golden_periodic_code_partition_seven :
    goldenPeriodicOrbitRepresentativesSeven.length = 12 ∧
      goldenEnumeratedOrbitStatesSeven.card = 60 := by
  norm_num [goldenPeriodicOrbitRepresentativesSeven]
  rw [golden_enumerated_orbit_states_eq_fixed_points]
  exact golden_periodic_point_code_count_seven

noncomputable def goldenDecodedOrbitStates (orbit : GoldenCodedOrbit) : List GoldenSurvivorState :=
  (goldenOrbitStates orbit).map decodeGoldenState

/-- Orbit-level completeness: every real periodic state of nonzero period at
most seven occurs on exactly one of the twelve displayed coded cycles. -/
theorem golden_periodic_orbit_enumeration_complete {period : Nat}
    (hperiodPos : 0 < period) (hperiodBound : period ≤ 7)
    (state : GoldenSurvivorState)
    (hperiod : (goldenTransition^[period]) state = state) :
    ∃ orbit ∈ goldenPeriodicOrbitRepresentativesSeven,
      state ∈ goldenDecodedOrbitStates orbit := by
  obtain ⟨code, hcode, rfl⟩ :=
    golden_periodic_point_enumeration_complete hperiodPos hperiodBound state hperiod
  have henumerated : code ∈ goldenEnumeratedOrbitStatesSeven := by
    rw [golden_enumerated_orbit_states_eq_fixed_points]
    exact hcode
  rw [goldenEnumeratedOrbitStatesSeven, List.mem_toFinset] at henumerated
  simp only [List.mem_flatMap] at henumerated
  obtain ⟨orbit, horbit, hcodeOrbit⟩ := henumerated
  refine ⟨orbit, horbit, ?_⟩
  rw [goldenDecodedOrbitStates, List.mem_map]
  exact ⟨code, hcodeOrbit, rfl⟩

set_option maxHeartbeats 1000000 in
-- The twelve selected low-arm comparisons expand all exact quadratic coordinates.
/-- The selected low state on every enumerated cycle has arm at most the
champion threshold. -/
theorem golden_periodic_orbit_low_arms_bounded :
    goldenPeriodicOrbitRepresentativesSeven.Forall fun orbit =>
      goldenStateArm (decodeGoldenState orbit.lowState) ≤ goldenThreshold := by
  have hphiRadical : φ = (1 + Real.sqrt 5) / 2 := rfl
  have hsqrtForm : 1 + Real.sqrt 5 = 2 * φ := by linarith [hphiRadical]
  rw [golden_threshold_eq, golden_inverse_sq]
  norm_num [goldenPeriodicOrbitRepresentativesSeven, goldenChampionPeriodicOrbit,
    goldenStateArm, decodeGoldenState, goldenCodeValue, qphi,
    golden_inverse_eq_sub_one, min_def]
  repeat' apply And.intro
  all_goals try split_ifs with h
  all_goals simp only [hsqrtForm] at *
  all_goals nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
    Real.goldenRatio_lt_two]

/-- A value is the attained minimum arm on a displayed finite orbit. -/
def GoldenOrbitMinimum (orbit : GoldenCodedOrbit) (value : Real) : Prop :=
  (∀ state ∈ goldenDecodedOrbitStates orbit, value ≤ goldenStateArm state) ∧
    ∃ state ∈ goldenDecodedOrbitStates orbit, goldenStateArm state = value

def goldenPeriodicOrbitMinimaSeven : Set Real :=
  {value | ∃ orbit ∈ goldenPeriodicOrbitRepresentativesSeven,
    GoldenOrbitMinimum orbit value}

theorem golden_champion_decoded_orbit_states :
    goldenDecodedOrbitStates goldenChampionPeriodicOrbit =
      [⟨.large, 1 / 2⟩, ⟨.large, φ / 2⟩, ⟨.small, 1 / 2⟩] := by
  norm_num [goldenDecodedOrbitStates, goldenChampionPeriodicOrbit,
    goldenOrbitStates, goldenTraceCode, goldenApplyStepCode, goldenStepAffine,
    goldenStepTarget, decodeGoldenState, goldenCodeValue, goldenCodeAdd,
    goldenCodeMul, goldenCodePhi, goldenCodeZero, goldenCodeOne, goldenCodeNeg,
    qphi]
  ring

/-- The period-three cycle attains the threshold as its minimum arm. -/
theorem golden_champion_periodic_orbit_minimum :
    GoldenOrbitMinimum goldenChampionPeriodicOrbit goldenThreshold := by
  rw [GoldenOrbitMinimum, golden_champion_decoded_orbit_states,
    golden_threshold_eq, golden_inverse_sq]
  constructor
  · intro state hstate
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hstate
    rcases hstate with rfl | rfl | rfl
    · norm_num [goldenStateArm]
      nlinarith [Real.one_lt_goldenRatio]
    · change (2 - φ) / 2 ≤ min (φ / 2) (1 - φ / 2)
      rw [min_eq_right (by nlinarith [Real.one_lt_goldenRatio])]
      ring_nf
      rfl
    · rw [goldenStateArm, golden_inverse_eq_sub_one]
      norm_num
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  · refine ⟨⟨.large, φ / 2⟩, by simp, ?_⟩
    change min (φ / 2) (1 - φ / 2) = (2 - φ) / 2
    rw [min_eq_right (by nlinarith [Real.one_lt_goldenRatio])]
    ring

/-- Every one of the twelve nonempty displayed cycles has an attained minimum. -/
theorem golden_periodic_orbit_minimum_exists (orbit : GoldenCodedOrbit)
    (horbit : orbit ∈ goldenPeriodicOrbitRepresentativesSeven) :
    ∃ value, GoldenOrbitMinimum orbit value := by
  have hcode := List.forall_iff_forall_mem.mp golden_periodic_orbit_low_states_mem
    orbit horbit
  have hstates : (goldenOrbitStates orbit).toFinset.Nonempty :=
    ⟨orbit.lowState, List.mem_toFinset.mpr hcode⟩
  obtain ⟨code, hstate, hleast⟩ :=
    Finset.exists_min_image (goldenOrbitStates orbit).toFinset
      (fun item => goldenStateArm (decodeGoldenState item)) hstates
  refine ⟨goldenStateArm (decodeGoldenState code), ⟨?_,
    decodeGoldenState code, ?_, rfl⟩⟩
  · intro other hother
    rw [goldenDecodedOrbitStates, List.mem_map] at hother
    obtain ⟨otherCode, hotherCode, rfl⟩ := hother
    exact hleast otherCode (List.mem_toFinset.mpr hotherCode)
  · rw [goldenDecodedOrbitStates, List.mem_map]
    exact ⟨code, List.mem_toFinset.mp hstate, rfl⟩

/-- The complete period-at-most-seven enumeration has maximin exactly
`phi^-2 / 2 = (2 - phi) / 2`. -/
theorem golden_periodic_orbit_maximin_seven :
    IsGreatest goldenPeriodicOrbitMinimaSeven goldenThreshold := by
  constructor
  · refine ⟨goldenChampionPeriodicOrbit, ?_,
      golden_champion_periodic_orbit_minimum⟩
    simp [goldenPeriodicOrbitRepresentativesSeven]
  · rintro value ⟨orbit, horbit, hminimum⟩
    have hlowCode := List.forall_iff_forall_mem.mp
      golden_periodic_orbit_low_states_mem orbit horbit
    have hlowDecoded : decodeGoldenState orbit.lowState ∈
        goldenDecodedOrbitStates orbit := by
      rw [goldenDecodedOrbitStates, List.mem_map]
      exact ⟨orbit.lowState, hlowCode, rfl⟩
    have hvalueLow := hminimum.1 _ hlowDecoded
    have hlowBound := List.forall_iff_forall_mem.mp
      golden_periodic_orbit_low_arms_bounded orbit horbit
    exact hvalueLow.trans hlowBound

end D5.S0.Tower.Champions.GoldenPeriodicEnumeration
