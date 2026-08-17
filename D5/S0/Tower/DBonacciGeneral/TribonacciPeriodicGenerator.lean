/- GID: D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicGenerator
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacciGeneral/TribonacciPeriodicGenerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact cubic codes and five certified branches enumerate Tribonacci periodic points. -/

import D5.S0.Tower.DBonacci.OrbitAlgebra

namespace D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen three-gap substitution, its typed
     d-bonacci refinement, and the period-two champion orbit, but no finite
     periodic enumeration or completeness theorem.
   * Pinned mathlib supplies finite lists, rational arithmetic, function
     iteration, and polynomial normalization. No theorem specializes them to
     this five-edge Tribonacci transition graph. -/

abbrev TribonacciPeriodicGap :=
  D5.S0.Tower.Tribonacci.Substitution.TribonacciGapLetter

/-- Gap lengths after removing the common level factor `t^-Q`. -/
noncomputable def tribonacciPeriodicGapLength : TribonacciPeriodicGap → Real
  | .large => 1
  | .small => t⁻¹
  | .combined => t - 1

/-- The five directed edges of the three-letter refinement graph. -/
inductive TribonacciPeriodicStep where
  | smallThrough
  | combinedLeft
  | combinedRight
  | largeLeft
  | largeRight
  deriving DecidableEq, Repr

def tribonacciStepSource : TribonacciPeriodicStep → TribonacciPeriodicGap
  | .smallThrough => .small
  | .combinedLeft | .combinedRight => .combined
  | .largeLeft | .largeRight => .large

def tribonacciStepTarget : TribonacciPeriodicStep → TribonacciPeriodicGap
  | .smallThrough | .combinedLeft | .largeLeft => .large
  | .combinedRight => .small
  | .largeRight => .combined

def tribonacciStepsFrom : TribonacciPeriodicGap → List TribonacciPeriodicStep
  | .small => [.smallThrough]
  | .combined => [.combinedLeft, .combinedRight]
  | .large => [.largeLeft, .largeRight]

/-- The branch graph is exactly the frozen Tribonacci gap substitution. -/
theorem tribonacci_steps_from_targets (gap : TribonacciPeriodicGap) :
    (tribonacciStepsFrom gap).map tribonacciStepTarget =
      D5.S0.Tower.Tribonacci.Substitution.gapLetterSubstitution gap := by
  cases gap <;> decide

/-- An exact code `(a,b,c)` denotes `a + b*t + c*t^2`. -/
structure TribonacciCubicCode where
  rational : ℚ
  linear : ℚ
  quadratic : ℚ
  deriving DecidableEq

@[ext]
theorem tribonacci_cubic_code_ext {x y : TribonacciCubicCode}
    (hrational : x.rational = y.rational)
    (hlinear : x.linear = y.linear)
    (hquadratic : x.quadratic = y.quadratic) : x = y := by
  cases x
  cases y
  simp_all

def tribonacciCodeZero : TribonacciCubicCode := ⟨0, 0, 0⟩

def tribonacciCodeOne : TribonacciCubicCode := ⟨1, 0, 0⟩

def tribonacciCodeRoot : TribonacciCubicCode := ⟨0, 1, 0⟩

def tribonacciCodeAdd (x y : TribonacciCubicCode) : TribonacciCubicCode :=
  ⟨x.rational + y.rational, x.linear + y.linear, x.quadratic + y.quadratic⟩

def tribonacciCodeNeg (x : TribonacciCubicCode) : TribonacciCubicCode :=
  ⟨-x.rational, -x.linear, -x.quadratic⟩

def tribonacciCodeSub (x y : TribonacciCubicCode) : TribonacciCubicCode :=
  tribonacciCodeAdd x (tribonacciCodeNeg y)

/-- Multiplication reduced by `t^3 = t^2 + t + 1`. -/
def tribonacciCodeMul (x y : TribonacciCubicCode) : TribonacciCubicCode :=
  let r0 := x.rational * y.rational
  let r1 := x.rational * y.linear + x.linear * y.rational
  let r2 := x.rational * y.quadratic + x.linear * y.linear +
    x.quadratic * y.rational
  let r3 := x.linear * y.quadratic + x.quadratic * y.linear
  let r4 := x.quadratic * y.quadratic
  ⟨r0 + r3 + r4, r1 + r3 + 2 * r4, r2 + r3 + 2 * r4⟩

def tribonacciCodeCofactorZero (x : TribonacciCubicCode) : ℚ :=
  (x.rational + x.quadratic) * (x.rational + x.linear + 2 * x.quadratic) -
    (x.linear + 2 * x.quadratic) * (x.linear + x.quadratic)

def tribonacciCodeCofactorOne (x : TribonacciCubicCode) : ℚ :=
  -(x.linear * (x.rational + x.linear + 2 * x.quadratic) -
    x.quadratic * (x.linear + 2 * x.quadratic))

def tribonacciCodeCofactorTwo (x : TribonacciCubicCode) : ℚ :=
  x.linear * (x.linear + x.quadratic) -
    x.quadratic * (x.rational + x.quadratic)

def tribonacciCodeNorm (x : TribonacciCubicCode) : ℚ :=
  x.rational * tribonacciCodeCofactorZero x +
    x.quadratic * tribonacciCodeCofactorOne x +
    (x.linear + x.quadratic) * tribonacciCodeCofactorTwo x

def tribonacciCodeInv (x : TribonacciCubicCode) : TribonacciCubicCode :=
  ⟨tribonacciCodeCofactorZero x / tribonacciCodeNorm x,
    tribonacciCodeCofactorOne x / tribonacciCodeNorm x,
    tribonacciCodeCofactorTwo x / tribonacciCodeNorm x⟩

def tribonacciCodeDiv (x y : TribonacciCubicCode) : TribonacciCubicCode :=
  tribonacciCodeMul x (tribonacciCodeInv y)

noncomputable def tribonacciCodeValue (x : TribonacciCubicCode) : Real :=
  (x.rational : Real) + (x.linear : Real) * t + (x.quadratic : Real) * t ^ 2

theorem tribonacci_code_value_add (x y : TribonacciCubicCode) :
    tribonacciCodeValue (tribonacciCodeAdd x y) =
      tribonacciCodeValue x + tribonacciCodeValue y := by
  simp [tribonacciCodeValue, tribonacciCodeAdd]
  ring

theorem tribonacci_code_value_neg (x : TribonacciCubicCode) :
    tribonacciCodeValue (tribonacciCodeNeg x) = -tribonacciCodeValue x := by
  simp [tribonacciCodeValue, tribonacciCodeNeg]
  ring

theorem tribonacci_code_value_sub (x y : TribonacciCubicCode) :
    tribonacciCodeValue (tribonacciCodeSub x y) =
      tribonacciCodeValue x - tribonacciCodeValue y := by
  rw [tribonacciCodeSub, tribonacci_code_value_add, tribonacci_code_value_neg]
  ring

theorem tribonacci_code_value_mul (x y : TribonacciCubicCode) :
    tribonacciCodeValue (tribonacciCodeMul x y) =
      tribonacciCodeValue x * tribonacciCodeValue y := by
  have hcubic : t ^ 3 = 1 + t + t ^ 2 := by
    nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic]
  have hfour : t ^ 4 = 1 + 2 * t + 2 * t ^ 2 := by
    calc
      t ^ 4 = t * t ^ 3 := by ring
      _ = t * (1 + t + t ^ 2) := by rw [hcubic]
      _ = 1 + 2 * t + 2 * t ^ 2 := by
        nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic]
  simp only [tribonacciCodeValue, tribonacciCodeMul]
  push_cast
  calc
    _ = (x.rational : Real) * y.rational +
        (x.rational * y.linear + x.linear * y.rational) * t +
        (x.rational * y.quadratic + x.linear * y.linear +
          x.quadratic * y.rational) * t ^ 2 +
        (x.linear * y.quadratic + x.quadratic * y.linear) *
          (1 + t + t ^ 2) +
        (x.quadratic * y.quadratic) * (1 + 2 * t + 2 * t ^ 2) := by ring
    _ = (x.rational : Real) * y.rational +
        (x.rational * y.linear + x.linear * y.rational) * t +
        (x.rational * y.quadratic + x.linear * y.linear +
          x.quadratic * y.rational) * t ^ 2 +
        (x.linear * y.quadratic + x.quadratic * y.linear) * t ^ 3 +
        (x.quadratic * y.quadratic) * t ^ 4 := by rw [hcubic, hfour]
    _ = ((x.rational : Real) + x.linear * t + x.quadratic * t ^ 2) *
        ((y.rational : Real) + y.linear * t + y.quadratic * t ^ 2) := by ring

theorem tribonacci_code_mul_inv (x : TribonacciCubicCode)
    (hnorm : tribonacciCodeNorm x ≠ 0) :
    tribonacciCodeMul x (tribonacciCodeInv x) = tribonacciCodeOne := by
  ext <;>
    simp only [tribonacciCodeMul, tribonacciCodeInv, tribonacciCodeOne] <;>
    field_simp [hnorm] <;>
    simp only [tribonacciCodeNorm, tribonacciCodeCofactorZero,
      tribonacciCodeCofactorOne, tribonacciCodeCofactorTwo] <;> ring

theorem tribonacci_code_value_inv (x : TribonacciCubicCode)
    (hnorm : tribonacciCodeNorm x ≠ 0) :
    tribonacciCodeValue (tribonacciCodeInv x) = (tribonacciCodeValue x)⁻¹ := by
  have hproduct : tribonacciCodeValue x * tribonacciCodeValue (tribonacciCodeInv x) = 1 := by
    rw [← tribonacci_code_value_mul, tribonacci_code_mul_inv x hnorm]
    norm_num [tribonacciCodeValue, tribonacciCodeOne]
  exact eq_inv_of_mul_eq_one_right hproduct

theorem tribonacci_code_value_div (x y : TribonacciCubicCode)
    (hnorm : tribonacciCodeNorm y ≠ 0) :
    tribonacciCodeValue (tribonacciCodeDiv x y) =
      tribonacciCodeValue x / tribonacciCodeValue y := by
  rw [tribonacciCodeDiv, tribonacci_code_value_mul,
    tribonacci_code_value_inv y hnorm, div_eq_mul_inv]

theorem tribonacci_code_value_ne_zero_of_norm_ne_zero (x : TribonacciCubicCode)
    (hnorm : tribonacciCodeNorm x ≠ 0) : tribonacciCodeValue x ≠ 0 := by
  intro hzero
  have hproduct : tribonacciCodeValue x * tribonacciCodeValue (tribonacciCodeInv x) = 1 := by
    rw [← tribonacci_code_value_mul, tribonacci_code_mul_inv x hnorm]
    norm_num [tribonacciCodeValue, tribonacciCodeOne]
  rw [hzero, zero_mul] at hproduct
  norm_num at hproduct

structure TribonacciAffineCode where
  multiplier : TribonacciCubicCode
  offset : TribonacciCubicCode
  deriving DecidableEq

def tribonacciIdentityAffine : TribonacciAffineCode :=
  ⟨tribonacciCodeOne, tribonacciCodeZero⟩

def tribonacciStepAffine : TribonacciPeriodicStep → TribonacciAffineCode
  | .smallThrough | .combinedLeft | .largeLeft =>
      ⟨tribonacciCodeRoot, tribonacciCodeZero⟩
  | .combinedRight | .largeRight =>
      ⟨tribonacciCodeRoot, tribonacciCodeNeg tribonacciCodeOne⟩

noncomputable def tribonacciStepCoordinate
    (step : TribonacciPeriodicStep) (u : Real) : Real :=
  match step with
  | .smallThrough | .combinedLeft | .largeLeft => t * u
  | .combinedRight | .largeRight => t * u - 1

theorem tribonacci_step_affine_value (step : TribonacciPeriodicStep) (u : Real) :
    tribonacciCodeValue (tribonacciStepAffine step).multiplier * u +
        tribonacciCodeValue (tribonacciStepAffine step).offset =
      tribonacciStepCoordinate step u := by
  cases step <;>
    norm_num [tribonacciStepAffine, tribonacciStepCoordinate,
      tribonacciCodeValue, tribonacciCodeRoot, tribonacciCodeZero,
      tribonacciCodeOne, tribonacciCodeNeg] <;> ring

/-- `outer` after `inner`. -/
def tribonacciAffineCompose
    (outer inner : TribonacciAffineCode) : TribonacciAffineCode :=
  ⟨tribonacciCodeMul outer.multiplier inner.multiplier,
    tribonacciCodeAdd (tribonacciCodeMul outer.multiplier inner.offset) outer.offset⟩

def tribonacciPathAffine (steps : List TribonacciPeriodicStep) : TribonacciAffineCode :=
  steps.foldl (fun affine step =>
    tribonacciAffineCompose (tribonacciStepAffine step) affine) tribonacciIdentityAffine

noncomputable def tribonacciPathCoordinate
    (steps : List TribonacciPeriodicStep) (u : Real) : Real :=
  steps.foldl (fun coordinate step => tribonacciStepCoordinate step coordinate) u

theorem tribonacci_path_affine_value_aux (steps : List TribonacciPeriodicStep)
    (affine : TribonacciAffineCode) (u : Real) :
    tribonacciCodeValue
          (steps.foldl (fun current step =>
            tribonacciAffineCompose (tribonacciStepAffine step) current) affine).multiplier * u +
        tribonacciCodeValue
          (steps.foldl (fun current step =>
            tribonacciAffineCompose (tribonacciStepAffine step) current) affine).offset =
      tribonacciPathCoordinate steps
        (tribonacciCodeValue affine.multiplier * u + tribonacciCodeValue affine.offset) := by
  induction steps generalizing affine with
  | nil => rfl
  | cons step rest ih =>
      simp only [List.foldl_cons, tribonacciPathCoordinate]
      rw [ih]
      simp only [tribonacciAffineCompose, tribonacci_code_value_mul,
        tribonacci_code_value_add]
      apply congrArg (tribonacciPathCoordinate rest)
      rw [← tribonacci_step_affine_value step
        (tribonacciCodeValue affine.multiplier * u + tribonacciCodeValue affine.offset)]
      ring

theorem tribonacci_path_affine_value (steps : List TribonacciPeriodicStep) (u : Real) :
    tribonacciCodeValue (tribonacciPathAffine steps).multiplier * u +
        tribonacciCodeValue (tribonacciPathAffine steps).offset =
      tribonacciPathCoordinate steps u := by
  rw [tribonacciPathAffine, tribonacci_path_affine_value_aux]
  norm_num [tribonacciIdentityAffine, tribonacciCodeValue,
    tribonacciCodeOne, tribonacciCodeZero]

def tribonacciPathCandidateCode (steps : List TribonacciPeriodicStep) :
    TribonacciCubicCode :=
  tribonacciCodeDiv (tribonacciPathAffine steps).offset
    (tribonacciCodeSub tribonacciCodeOne (tribonacciPathAffine steps).multiplier)

/-- All graph-compatible paths of exactly the requested length. -/
def tribonacciPathsFrom : TribonacciPeriodicGap → Nat →
    List (List TribonacciPeriodicStep × TribonacciPeriodicGap)
  | gap, 0 => [([], gap)]
  | .small, period + 1 =>
      (tribonacciPathsFrom .large period).map
        (fun path => (.smallThrough :: path.1, path.2))
  | .combined, period + 1 =>
      (tribonacciPathsFrom .large period).map
          (fun path => (.combinedLeft :: path.1, path.2)) ++
        (tribonacciPathsFrom .small period).map
          (fun path => (.combinedRight :: path.1, path.2))
  | .large, period + 1 =>
      (tribonacciPathsFrom .large period).map
          (fun path => (.largeLeft :: path.1, path.2)) ++
        (tribonacciPathsFrom .combined period).map
          (fun path => (.largeRight :: path.1, path.2))

def tribonacciClosedFrom (gap : TribonacciPeriodicGap) (period : Nat) :
    List (TribonacciPeriodicGap × List TribonacciPeriodicStep) :=
  (tribonacciPathsFrom gap period).filterMap fun path =>
    if path.2 = gap then some (gap, path.1) else none

def tribonacciClosedItineraries (period : Nat) :
    List (TribonacciPeriodicGap × List TribonacciPeriodicStep) :=
  tribonacciClosedFrom .large period ++
    tribonacciClosedFrom .small period ++
    tribonacciClosedFrom .combined period

structure TribonacciPeriodicState where
  kind : TribonacciPeriodicGap
  coordinate : Real

noncomputable def tribonacciPeriodicTransition
    (state : TribonacciPeriodicState) : TribonacciPeriodicState :=
  match state.kind with
  | .small => ⟨.large, t * state.coordinate⟩
  | .combined =>
      if state.coordinate ≤ t⁻¹ then
        ⟨.large, t * state.coordinate⟩
      else
        ⟨.small, t * state.coordinate - 1⟩
  | .large =>
      if state.coordinate ≤ t⁻¹ then
        ⟨.large, t * state.coordinate⟩
      else
        ⟨.combined, t * state.coordinate - 1⟩

noncomputable def tribonacciActualSteps : Nat → TribonacciPeriodicState →
    List TribonacciPeriodicStep
  | 0, _ => []
  | period + 1, state =>
      match state.kind with
      | .small => .smallThrough ::
          tribonacciActualSteps period (tribonacciPeriodicTransition state)
      | .combined =>
          if state.coordinate ≤ t⁻¹ then
            .combinedLeft :: tribonacciActualSteps period (tribonacciPeriodicTransition state)
          else
            .combinedRight :: tribonacciActualSteps period (tribonacciPeriodicTransition state)
      | .large =>
          if state.coordinate ≤ t⁻¹ then
            .largeLeft :: tribonacciActualSteps period (tribonacciPeriodicTransition state)
          else
            .largeRight :: tribonacciActualSteps period (tribonacciPeriodicTransition state)

theorem tribonacci_actual_steps_length (period : Nat) (state : TribonacciPeriodicState) :
    (tribonacciActualSteps period state).length = period := by
  induction period generalizing state with
  | zero => rfl
  | succ period ih =>
      cases state with
      | mk kind coordinate =>
          cases kind <;> simp only [tribonacciActualSteps, List.length_cons]
          · split <;> simp [ih]
          · simp [ih]
          · split <;> simp [ih]

theorem tribonacci_actual_steps_mem_paths (period : Nat) (state : TribonacciPeriodicState) :
    (tribonacciActualSteps period state,
        ((tribonacciPeriodicTransition^[period]) state).kind) ∈
      tribonacciPathsFrom state.kind period := by
  induction period generalizing state with
  | zero => simp [tribonacciActualSteps, tribonacciPathsFrom]
  | succ period ih =>
      rw [Function.iterate_succ_apply]
      cases state with
      | mk kind coordinate =>
          cases kind
          · simp only [tribonacciActualSteps, tribonacciPathsFrom, List.mem_append,
              List.mem_map, tribonacciPeriodicTransition]
            split_ifs with hbranch
            · left
              exact ⟨_, ih ⟨.large, t * coordinate⟩, rfl⟩
            · right
              exact ⟨_, ih ⟨.combined, t * coordinate - 1⟩, rfl⟩
          · simp only [tribonacciActualSteps, tribonacciPathsFrom, List.mem_map,
              tribonacciPeriodicTransition]
            exact ⟨_, ih ⟨.large, t * coordinate⟩, rfl⟩
          · simp only [tribonacciActualSteps, tribonacciPathsFrom, List.mem_append,
              List.mem_map, tribonacciPeriodicTransition]
            split_ifs with hbranch
            · left
              exact ⟨_, ih ⟨.large, t * coordinate⟩, rfl⟩
            · right
              exact ⟨_, ih ⟨.small, t * coordinate - 1⟩, rfl⟩

theorem tribonacci_actual_steps_coordinate (period : Nat) (state : TribonacciPeriodicState) :
    tribonacciPathCoordinate (tribonacciActualSteps period state) state.coordinate =
      ((tribonacciPeriodicTransition^[period]) state).coordinate := by
  induction period generalizing state with
  | zero => rfl
  | succ period ih =>
      rw [Function.iterate_succ_apply]
      cases state with
      | mk kind coordinate =>
          cases kind
          · simp only [tribonacciActualSteps, tribonacciPathCoordinate,
              tribonacciPeriodicTransition]
            split_ifs with hbranch
            · change tribonacciPathCoordinate
                (tribonacciActualSteps period
                  (⟨.large, t * coordinate⟩ : TribonacciPeriodicState))
                  (t * coordinate) = _
              exact ih _
            · change tribonacciPathCoordinate
                (tribonacciActualSteps period
                  (⟨.combined, t * coordinate - 1⟩ : TribonacciPeriodicState))
                  (t * coordinate - 1) = _
              exact ih _
          · simp only [tribonacciActualSteps, tribonacciPathCoordinate,
              List.foldl_cons, tribonacciPeriodicTransition]
            change tribonacciPathCoordinate
              (tribonacciActualSteps period
                (⟨.large, t * coordinate⟩ : TribonacciPeriodicState))
                (t * coordinate) = _
            exact ih _
          · simp only [tribonacciActualSteps, tribonacciPathCoordinate,
              tribonacciPeriodicTransition]
            split_ifs with hbranch
            · change tribonacciPathCoordinate
                (tribonacciActualSteps period
                  (⟨.large, t * coordinate⟩ : TribonacciPeriodicState))
                  (t * coordinate) = _
              exact ih _
            · change tribonacciPathCoordinate
                (tribonacciActualSteps period
                  (⟨.small, t * coordinate - 1⟩ : TribonacciPeriodicState))
                  (t * coordinate - 1) = _
              exact ih _

theorem tribonacci_actual_steps_mem_closed {period : Nat}
    {state : TribonacciPeriodicState}
    (hperiod : (tribonacciPeriodicTransition^[period]) state = state) :
    (state.kind, tribonacciActualSteps period state) ∈
      tribonacciClosedItineraries period := by
  have hpaths := tribonacci_actual_steps_mem_paths period state
  have hkind : ((tribonacciPeriodicTransition^[period]) state).kind = state.kind :=
    congrArg TribonacciPeriodicState.kind hperiod
  have hfilter :
      (state.kind, tribonacciActualSteps period state) ∈
        tribonacciClosedFrom state.kind period := by
    rw [tribonacciClosedFrom]
    simp only [List.mem_filterMap]
    exact ⟨_, hpaths, by simp [hkind]⟩
  simp only [tribonacciClosedItineraries, List.mem_append]
  cases hstateKind : state.kind
  · exact Or.inl (Or.inl (by simpa only [hstateKind] using hfilter))
  · exact Or.inl (Or.inr (by simpa only [hstateKind] using hfilter))
  · exact Or.inr (by simpa only [hstateKind] using hfilter)

structure TribonacciCodedState where
  kind : TribonacciPeriodicGap
  coordinate : TribonacciCubicCode
  deriving DecidableEq

noncomputable def decodeTribonacciState
    (state : TribonacciCodedState) : TribonacciPeriodicState :=
  ⟨state.kind, tribonacciCodeValue state.coordinate⟩

def tribonacciFixedPointCodes (period : Nat) : List TribonacciCodedState :=
  (tribonacciClosedItineraries period).map fun itinerary =>
    ⟨itinerary.1, tribonacciPathCandidateCode itinerary.2⟩

/-- Once its exact cubic denominator is certified nonzero, every real periodic
state is the decoded fixed point attached to its generated branch word. -/
theorem tribonacci_periodic_point_enumeration_complete {period : Nat}
    (state : TribonacciPeriodicState)
    (hperiod : (tribonacciPeriodicTransition^[period]) state = state)
    (hnorm : tribonacciCodeNorm
      (tribonacciCodeSub tribonacciCodeOne
        (tribonacciPathAffine (tribonacciActualSteps period state)).multiplier) ≠ 0) :
    ∃ code ∈ tribonacciFixedPointCodes period,
      state = decodeTribonacciState code := by
  let steps := tribonacciActualSteps period state
  have hitinerary : (state.kind, steps) ∈ tribonacciClosedItineraries period :=
    tribonacci_actual_steps_mem_closed hperiod
  have hclosedCoordinate : tribonacciPathCoordinate steps state.coordinate =
      state.coordinate := by
    calc
      tribonacciPathCoordinate steps state.coordinate =
          ((tribonacciPeriodicTransition^[period]) state).coordinate :=
        tribonacci_actual_steps_coordinate period state
      _ = state.coordinate := congrArg TribonacciPeriodicState.coordinate hperiod
  have haffine := tribonacci_path_affine_value steps state.coordinate
  rw [hclosedCoordinate] at haffine
  have hdenValue : tribonacciCodeValue
      (tribonacciCodeSub tribonacciCodeOne
        (tribonacciPathAffine steps).multiplier) ≠ 0 :=
    tribonacci_code_value_ne_zero_of_norm_ne_zero _ hnorm
  have hcandidate : tribonacciCodeValue (tribonacciPathCandidateCode steps) =
      state.coordinate := by
    rw [tribonacciPathCandidateCode, tribonacci_code_value_div _ _ hnorm]
    apply (div_eq_iff hdenValue).2
    rw [tribonacci_code_value_sub]
    have hone : tribonacciCodeValue tribonacciCodeOne = 1 := by
      norm_num [tribonacciCodeValue, tribonacciCodeOne]
    rw [hone]
    linear_combination haffine
  let code : TribonacciCodedState :=
    ⟨state.kind, tribonacciPathCandidateCode steps⟩
  refine ⟨code, ?_, ?_⟩
  · simp only [tribonacciFixedPointCodes, List.mem_map]
    exact ⟨(state.kind, steps), hitinerary, rfl⟩
  · cases state with
    | mk kind coordinate =>
        simp only [code, decodeTribonacciState]
        rw [hcandidate]

end D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
