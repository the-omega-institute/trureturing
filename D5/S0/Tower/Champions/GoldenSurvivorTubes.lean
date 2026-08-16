/- GID: D5/S0/Tower/Champions/GoldenSurvivorTubes
   generality: I
   mirror-B: D5/B/S0/Tower/Champions/GoldenSurvivorTubes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Backward golden-gap survival has four contracting limit branches. -/

import D5.S0.Tower.GoldenGapWord
import D5.S0.Tower.MetricGeometry.GoldenSurvivor
import Mathlib.Order.Filter.ENNReal

/- Library-search audit trail (2026-08-16):
   * Repository search found the frozen gap substitution, completed gap word,
     real-line survivor carrier, and the r60a champion orbit proof, but no
     backward-survivor or graph-directed contraction classification.
   * Pinned mathlib supplies `Function.iterate`, set preimages, real `liminf`,
     and elementary contraction algebra, but no theorem specialized to this
     piecewise golden map.
   * Loogle/LeanSearch names checked locally included `Filter.liminf_le_iff`,
     `Real.liminf_of_not_isCoboundedUnder`, and `Metric.le_infDist`; none
     identifies the four golden survivor branches.  The finite-state argument
     is therefore proved in this module. -/

namespace D5.S0.Tower.Champions.GoldenSurvivorTubes

local notation "φ" => Real.goldenRatio

/-- The two normalized golden gap types. -/
inductive GoldenGapKind where
  | large
  | small
  deriving DecidableEq

/-- A gap type together with position as a fraction of that gap. -/
structure GoldenSurvivorState where
  kind : GoldenGapKind
  coordinate : Real

/-- The inverse golden ratio, used as the small-to-large length ratio. -/
noncomputable def goldenInverse : Real := φ ^ (-1 : Int)

/-- The proposed asymptotic threshold. -/
noncomputable def goldenThreshold : Real := φ ^ (-2 : Int) / 2

theorem golden_inverse_eq_sub_one : goldenInverse = φ - 1 := by
  rw [goldenInverse, zpow_neg, zpow_one, Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

theorem golden_inverse_mul : goldenInverse * φ = 1 := by
  rw [golden_inverse_eq_sub_one]
  nlinarith [Real.goldenRatio_sq]

theorem golden_inverse_sq : goldenInverse ^ 2 = 2 - φ := by
  rw [golden_inverse_eq_sub_one]
  nlinarith [Real.goldenRatio_sq]

theorem golden_threshold_eq : goldenThreshold = goldenInverse ^ 2 / 2 := by
  rw [goldenThreshold, zpow_neg]
  norm_num only [zpow_ofNat]
  rw [show (φ ^ 2)⁻¹ = goldenInverse ^ 2 by
    rw [goldenInverse, zpow_neg, zpow_one, inv_pow]]

theorem golden_inverse_pos : 0 < goldenInverse := by
  rw [goldenInverse]
  positivity

theorem golden_inverse_lt_one : goldenInverse < 1 := by
  rw [goldenInverse, zpow_neg, zpow_one]
  exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio

theorem golden_half_le_inverse : (1 : Real) / 2 ≤ goldenInverse := by
  rw [golden_inverse_eq_sub_one]
  have hφ : (3 : Real) / 2 ≤ φ := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  linarith

theorem golden_inverse_lt_phi_half : goldenInverse < φ / 2 := by
  rw [golden_inverse_eq_sub_one]
  have hφ : φ < 2 := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  linarith

theorem golden_inverse_half_le_inverse : goldenInverse / 2 ≤ goldenInverse := by
  linarith [golden_inverse_pos]

/-- Normalized distance to the nearer endpoint of a typed gap. -/
noncomputable def goldenStateArm (state : GoldenSurvivorState) : Real :=
  match state.kind with
  | .large => min state.coordinate (1 - state.coordinate)
  | .small => goldenInverse * min state.coordinate (1 - state.coordinate)

/-- The open survivor domain from the source argument. -/
def goldenStrictSurvivorSet : Set GoldenSurvivorState :=
  {state | goldenThreshold < goldenStateArm state}

/-- The closed threshold domain used when taking finite-depth limits. -/
def goldenClosedSurvivorSet : Set GoldenSurvivorState :=
  {state | goldenThreshold ≤ goldenStateArm state}

/-- Refinement of a local gap coordinate.  Large gaps split at `phi^-1`;
small gaps become large without changing their fractional coordinate. -/
noncomputable def goldenTransition (state : GoldenSurvivorState) : GoldenSurvivorState :=
  match state.kind with
  | .large =>
      if state.coordinate ≤ goldenInverse then
        ⟨.large, φ * state.coordinate⟩
      else
        ⟨.small, φ ^ 2 * state.coordinate - φ⟩
  | .small => ⟨.large, state.coordinate⟩

/-- Finite backward survival.  The successor clause uses the preimage `T⁻¹`,
not the forward image `T '' S`. -/
noncomputable def goldenBackwardSurvivor
    (F : Set GoldenSurvivorState) : Nat → Set GoldenSurvivorState
  | 0 => F
  | n + 1 => F ∩ goldenTransition ⁻¹' goldenBackwardSurvivor F n

theorem golden_backward_survivor_succ (F : Set GoldenSurvivorState) (n : Nat) :
    goldenBackwardSurvivor F (n + 1) =
      F ∩ goldenTransition ⁻¹' goldenBackwardSurvivor F n := by
  simp [goldenBackwardSurvivor]

/-- The four active inverse branches after the finite transient.  The first
two have the same affine formula but different component domains. -/
inductive GoldenBackwardBranch where
  | tail
  | largeCycle
  | rightCycle
  | smallCycle
  deriving DecidableEq

def goldenBranchTargetKind : GoldenBackwardBranch → GoldenGapKind
  | .tail | .largeCycle | .smallCycle => .large
  | .rightCycle => .small

def goldenBranchSourceKind : GoldenBackwardBranch → GoldenGapKind
  | .tail | .largeCycle | .rightCycle => .large
  | .smallCycle => .small

noncomputable def goldenBranchCoordinate
    (branch : GoldenBackwardBranch) (u : Real) : Real :=
  match branch with
  | .tail | .largeCycle => goldenInverse * u
  | .rightCycle => goldenInverse ^ 2 * (u + φ)
  | .smallCycle => u

/-- Fiber distance weights the short chart by its physical length ratio. -/
noncomputable def goldenFiberDistance (kind : GoldenGapKind) (u v : Real) : Real :=
  match kind with
  | .large => |u - v|
  | .small => goldenInverse * |u - v|

/-- Every one of the four active affine inverse branches contracts physical
fiber distance by exactly `phi^-1`. -/
theorem golden_backward_branch_contraction
    (branch : GoldenBackwardBranch) (u v : Real) :
    goldenFiberDistance (goldenBranchSourceKind branch)
        (goldenBranchCoordinate branch u) (goldenBranchCoordinate branch v) =
      goldenInverse * goldenFiberDistance (goldenBranchTargetKind branch) u v := by
  cases branch
  · simp only [goldenBranchSourceKind, goldenBranchTargetKind,
      goldenBranchCoordinate, goldenFiberDistance]
    calc
      |goldenInverse * u - goldenInverse * v| = |goldenInverse * (u - v)| := by
        congr 1
        ring
      _ = goldenInverse * |u - v| := by
        rw [abs_mul, abs_of_pos golden_inverse_pos]
  · simp only [goldenBranchSourceKind, goldenBranchTargetKind,
      goldenBranchCoordinate, goldenFiberDistance]
    calc
      |goldenInverse * u - goldenInverse * v| = |goldenInverse * (u - v)| := by
        congr 1
        ring
      _ = goldenInverse * |u - v| := by
        rw [abs_mul, abs_of_pos golden_inverse_pos]
  · simp only [goldenBranchSourceKind, goldenBranchTargetKind,
      goldenBranchCoordinate, goldenFiberDistance]
    calc
      |goldenInverse ^ 2 * (u + φ) - goldenInverse ^ 2 * (v + φ)| =
          |goldenInverse ^ 2 * (u - v)| := by
        congr 1
        ring
      _ = goldenInverse * (goldenInverse * |u - v|) := by
        rw [abs_mul, abs_of_pos (sq_pos_of_pos golden_inverse_pos)]
        ring
  · rfl

/-- A rational upper enclosure for the independently computed contraction. -/
theorem golden_inverse_lt_619_div_1000 :
    goldenInverse < (619 : Real) / 1000 := by
  rw [golden_inverse_eq_sub_one]
  have hφ : φ < (1619 : Real) / 1000 := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  linarith

/-- Forty inverse steps have contraction factor below `5e-9`. -/
theorem golden_depth_forty_contraction_lt :
    goldenInverse ^ 40 < (5 : Real) / 1000000000 := by
  calc
    goldenInverse ^ 40 < ((619 : Real) / 1000) ^ 40 := by
      gcongr
      · exact golden_inverse_pos.le
      · exact golden_inverse_lt_619_div_1000
    _ < (5 : Real) / 1000000000 := by norm_num

example : ((619 : Real) / 1000) ^ 40 < (5 : Real) / 1000000000 := by
  norm_num

/-- The one-step preimage of the large midpoint. -/
noncomputable def goldenTailPoint : GoldenSurvivorState :=
  ⟨.large, goldenInverse / 2⟩

/-- The large midpoint in the champion cycle. -/
noncomputable def goldenLargeMidpoint : GoldenSurvivorState :=
  ⟨.large, 1 / 2⟩

/-- The second large-gap coordinate in the champion cycle. -/
noncomputable def goldenLargePhiPoint : GoldenSurvivorState :=
  ⟨.large, φ / 2⟩

/-- The small midpoint in the champion cycle. -/
noncomputable def goldenSmallMidpoint : GoldenSurvivorState :=
  ⟨.small, 1 / 2⟩

/-- The four limiting component centers seen by backward survival. -/
def goldenFourPointSet : Set GoldenSurvivorState :=
  {goldenTailPoint, goldenLargeMidpoint, goldenLargePhiPoint, goldenSmallMidpoint}

theorem golden_one_sub_threshold : 1 - goldenThreshold = φ / 2 := by
  rw [golden_threshold_eq, golden_inverse_sq]
  ring

theorem golden_strict_large_iff (u : Real) :
    (⟨.large, u⟩ : GoldenSurvivorState) ∈ goldenStrictSurvivorSet ↔
      goldenThreshold < u ∧ u < φ / 2 := by
  change goldenThreshold < min u (1 - u) ↔ _
  rw [lt_min_iff]
  constructor
  · intro h
    exact ⟨h.1, by rw [← golden_one_sub_threshold]; linarith⟩
  · intro h
    exact ⟨h.1, by nlinarith [golden_one_sub_threshold]⟩

theorem golden_strict_small_iff (u : Real) :
    (⟨.small, u⟩ : GoldenSurvivorState) ∈ goldenStrictSurvivorSet ↔
      goldenInverse / 2 < u ∧ u < 1 - goldenInverse / 2 := by
  change goldenThreshold < goldenInverse * min u (1 - u) ↔ _
  rw [golden_threshold_eq]
  have ha := golden_inverse_pos
  constructor
  · intro h
    have hmin : goldenInverse / 2 < min u (1 - u) := by
      nlinarith
    exact ⟨(lt_min_iff.mp hmin).1, by linarith [(lt_min_iff.mp hmin).2]⟩
  · intro h
    have hmin : goldenInverse / 2 < min u (1 - u) :=
      lt_min h.1 (by linarith [h.2])
    nlinarith

theorem golden_closed_large_iff (u : Real) :
    (⟨.large, u⟩ : GoldenSurvivorState) ∈ goldenClosedSurvivorSet ↔
      goldenThreshold ≤ u ∧ u ≤ φ / 2 := by
  change goldenThreshold ≤ min u (1 - u) ↔ _
  rw [le_min_iff]
  constructor
  · intro h
    exact ⟨h.1, by rw [← golden_one_sub_threshold]; linarith⟩
  · intro h
    exact ⟨h.1, by nlinarith [golden_one_sub_threshold]⟩

theorem golden_closed_small_iff (u : Real) :
    (⟨.small, u⟩ : GoldenSurvivorState) ∈ goldenClosedSurvivorSet ↔
      goldenInverse / 2 ≤ u ∧ u ≤ 1 - goldenInverse / 2 := by
  change goldenThreshold ≤ goldenInverse * min u (1 - u) ↔ _
  rw [golden_threshold_eq]
  have ha := golden_inverse_pos
  constructor
  · intro h
    have hmin : goldenInverse / 2 ≤ min u (1 - u) := by
      nlinarith
    exact ⟨(le_min_iff.mp hmin).1, by linarith [(le_min_iff.mp hmin).2]⟩
  · intro h
    have hmin : goldenInverse / 2 ≤ min u (1 - u) :=
      le_min h.1 (by linarith [h.2])
    nlinarith

/-- Lower endpoints of the four nondegenerate finite-depth components. -/
structure GoldenTubeLows where
  tail : Real
  midpoint : Real
  phiPoint : Real
  small : Real

noncomputable def goldenInitialTubeLows : GoldenTubeLows where
  tail := goldenThreshold
  midpoint := (9 - 5 * φ) / 2
  phiPoint := (4 * φ - 5) / 2
  small := goldenInverse / 2

noncomputable def goldenTubeStep (lows : GoldenTubeLows) : GoldenTubeLows where
  tail := goldenInverse * lows.midpoint
  midpoint := goldenInverse * lows.phiPoint
  phiPoint := goldenInverse ^ 2 * (lows.small + φ)
  small := lows.midpoint

noncomputable def goldenTubeLows : Nat → GoldenTubeLows
  | 0 => goldenInitialTubeLows
  | n + 1 => goldenTubeStep (goldenTubeLows n)

/-- The four open components remaining after the two-level transient. -/
def goldenOpenTube (n : Nat) (state : GoldenSurvivorState) : Prop :=
  match state.kind with
  | .large =>
      (goldenTubeLows n).tail < state.coordinate ∧
          state.coordinate < goldenInverse / 2 ∨
        (goldenTubeLows n).midpoint < state.coordinate ∧
          state.coordinate < 1 / 2 ∨
        (goldenTubeLows n).phiPoint < state.coordinate ∧
          state.coordinate < φ / 2
  | .small =>
      (goldenTubeLows n).small < state.coordinate ∧ state.coordinate < 1 / 2

/-- Componentwise closure of the four finite-depth tubes. -/
def goldenClosedTube (n : Nat) (state : GoldenSurvivorState) : Prop :=
  match state.kind with
  | .large =>
      (goldenTubeLows n).tail ≤ state.coordinate ∧
          state.coordinate ≤ goldenInverse / 2 ∨
        (goldenTubeLows n).midpoint ≤ state.coordinate ∧
          state.coordinate ≤ 1 / 2 ∨
        (goldenTubeLows n).phiPoint ≤ state.coordinate ∧
          state.coordinate ≤ φ / 2
  | .small =>
      (goldenTubeLows n).small ≤ state.coordinate ∧ state.coordinate ≤ 1 / 2

theorem golden_right_branch_center :
    goldenInverse ^ 2 * ((1 : Real) / 2 + φ) = φ / 2 := by
  rw [golden_inverse_sq]
  nlinarith [Real.goldenRatio_sq]

theorem golden_initial_phi_lower_gt_inverse :
    goldenInverse < goldenInitialTubeLows.phiPoint := by
  simp only [goldenInitialTubeLows]
  rw [golden_inverse_eq_sub_one]
  have hφ : (3 : Real) / 2 < φ := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  linarith

theorem golden_tube_lows_bounds (n : Nat) :
    goldenThreshold ≤ (goldenTubeLows n).tail ∧
      (goldenTubeLows n).tail < goldenInverse / 2 ∧
      goldenInverse / 2 < (goldenTubeLows n).midpoint ∧
      (goldenTubeLows n).midpoint < 1 / 2 ∧
      goldenInverse < (goldenTubeLows n).phiPoint ∧
      (goldenTubeLows n).phiPoint < φ / 2 ∧
      goldenInverse / 2 ≤ (goldenTubeLows n).small ∧
      (goldenTubeLows n).small < 1 / 2 := by
  induction n with
  | zero =>
      simp only [goldenTubeLows, goldenInitialTubeLows]
      rw [golden_inverse_eq_sub_one, goldenThreshold, zpow_neg]
      norm_num only [zpow_ofNat]
      have hφlo : (3 : Real) / 2 < φ := by
        nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
      have hφhi : φ < (5 : Real) / 3 := by
        nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
      have hpow : (φ ^ 2)⁻¹ = 2 - φ := by
        apply inv_eq_of_mul_eq_one_right
        nlinarith [Real.goldenRatio_sq]
      rw [hpow]
      constructor
      · nlinarith [Real.goldenRatio_sq]
      constructor
      · nlinarith [Real.goldenRatio_sq]
      constructor
      · nlinarith [Real.goldenRatio_sq]
      constructor
      · nlinarith [Real.goldenRatio_sq]
      constructor
      · nlinarith [Real.goldenRatio_sq]
      constructor
      · nlinarith [Real.goldenRatio_sq]
      constructor <;> nlinarith [Real.goldenRatio_sq]
  | succ n ih =>
      simp only [goldenTubeLows, goldenTubeStep]
      rcases ih with ⟨hAt, hAt', hBm, hBm', hCp, hCp', hDs, hDs'⟩
      have ha := golden_inverse_pos
      have ha1 := golden_inverse_lt_one
      have hahalf := golden_half_le_inverse
      have hcenterA : goldenInverse * ((1 : Real) / 2) = goldenInverse / 2 := by ring
      have hcenterB : goldenInverse * (φ / 2) = (1 : Real) / 2 := by
        nlinarith [golden_inverse_mul]
      have hbaseC : goldenInverse <
          goldenInverse ^ 2 * (goldenInverse / 2 + φ) := by
        rw [golden_inverse_sq, golden_inverse_eq_sub_one]
        nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
      constructor
      · rw [golden_threshold_eq]
        nlinarith
      constructor
      · nlinarith [hcenterA]
      constructor
      · have haa : goldenInverse / 2 < goldenInverse ^ 2 := by
          nlinarith [golden_inverse_sq, golden_inverse_eq_sub_one,
            Real.goldenRatio_sq, Real.one_lt_goldenRatio]
        nlinarith
      constructor
      · nlinarith [hcenterB]
      constructor
      · nlinarith [hbaseC]
      constructor
      · nlinarith [golden_right_branch_center]
      · exact ⟨hBm.le, hBm'⟩

theorem golden_tube_radii (n : Nat) :
    goldenInverse / 2 - (goldenTubeLows n).tail ≤ goldenInverse ^ n ∧
      (1 : Real) / 2 - (goldenTubeLows n).midpoint ≤ goldenInverse ^ n ∧
      φ / 2 - (goldenTubeLows n).phiPoint ≤ goldenInverse ^ n ∧
      goldenInverse * ((1 : Real) / 2 - (goldenTubeLows n).small) ≤
        goldenInverse ^ n := by
  induction n with
  | zero =>
      simp only [goldenTubeLows, goldenInitialTubeLows, pow_zero]
      have ha := golden_inverse_pos
      rw [golden_threshold_eq, golden_inverse_sq, golden_inverse_eq_sub_one]
      constructor
      · nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
      constructor
      · nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
      constructor
      · nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
      · nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  | succ n ih =>
      simp only [goldenTubeLows, goldenTubeStep, pow_succ]
      rcases ih with ⟨hA, hB, hC, hD⟩
      have ha := golden_inverse_pos
      have hcenterA : goldenInverse / 2 = goldenInverse * ((1 : Real) / 2) := by ring
      have hcenterB : (1 : Real) / 2 = goldenInverse * (φ / 2) := by
        nlinarith [golden_inverse_mul]
      constructor
      · nlinarith [hcenterA]
      constructor
      · nlinarith [hcenterB]
      constructor
      · have hscaled := mul_le_mul_of_nonneg_left hD ha.le
        nlinarith [golden_right_branch_center]
      · nlinarith

theorem golden_left_lower_iff (x u : Real) :
    x < φ * u ↔ goldenInverse * x < u := by
  constructor
  · intro h
    have hscaled := mul_lt_mul_of_pos_left h golden_inverse_pos
    calc
      goldenInverse * x < goldenInverse * (φ * u) := hscaled
      _ = u := by rw [← mul_assoc, golden_inverse_mul, one_mul]
  · intro h
    have hscaled := mul_lt_mul_of_pos_left h Real.goldenRatio_pos
    calc
      x = φ * (goldenInverse * x) := by
        rw [show φ * (goldenInverse * x) = (goldenInverse * φ) * x by ring,
          golden_inverse_mul, one_mul]
      _ < φ * u := hscaled

theorem golden_left_upper_iff (u y : Real) :
    φ * u < y ↔ u < goldenInverse * y := by
  constructor
  · intro h
    have hscaled := mul_lt_mul_of_pos_left h golden_inverse_pos
    calc
      u = goldenInverse * (φ * u) := by
        rw [← mul_assoc, golden_inverse_mul, one_mul]
      _ < goldenInverse * y := hscaled
  · intro h
    have hscaled := mul_lt_mul_of_pos_left h Real.goldenRatio_pos
    calc
      φ * u < φ * (goldenInverse * y) := hscaled
      _ = y := by
        rw [show φ * (goldenInverse * y) = (goldenInverse * φ) * y by ring,
          golden_inverse_mul, one_mul]

theorem golden_inverse_sq_mul_phi_sq : goldenInverse ^ 2 * φ ^ 2 = 1 := by
  rw [← mul_pow, golden_inverse_mul]
  norm_num

theorem golden_right_lower_iff (x u : Real) :
    x < φ ^ 2 * u - φ ↔ goldenInverse ^ 2 * (x + φ) < u := by
  have ha2 : 0 < goldenInverse ^ 2 := sq_pos_of_pos golden_inverse_pos
  have hφ2 : 0 < φ ^ 2 := sq_pos_of_pos Real.goldenRatio_pos
  constructor
  · intro h
    have hscaled := mul_lt_mul_of_pos_left (by linarith : x + φ < φ ^ 2 * u) ha2
    calc
      goldenInverse ^ 2 * (x + φ) < goldenInverse ^ 2 * (φ ^ 2 * u) := hscaled
      _ = u := by rw [← mul_assoc, golden_inverse_sq_mul_phi_sq, one_mul]
  · intro h
    have hscaled := mul_lt_mul_of_pos_left h hφ2
    have hcomm : φ ^ 2 * goldenInverse ^ 2 = 1 := by
      rw [mul_comm, golden_inverse_sq_mul_phi_sq]
    have : x + φ < φ ^ 2 * u := by
      calc
        x + φ = φ ^ 2 * (goldenInverse ^ 2 * (x + φ)) := by
          rw [← mul_assoc, hcomm, one_mul]
        _ < φ ^ 2 * u := hscaled
    linarith

theorem golden_right_upper_iff (u y : Real) :
    φ ^ 2 * u - φ < y ↔ u < goldenInverse ^ 2 * (y + φ) := by
  have ha2 : 0 < goldenInverse ^ 2 := sq_pos_of_pos golden_inverse_pos
  have hφ2 : 0 < φ ^ 2 := sq_pos_of_pos Real.goldenRatio_pos
  constructor
  · intro h
    have hscaled := mul_lt_mul_of_pos_left (by linarith : φ ^ 2 * u < y + φ) ha2
    calc
      u = goldenInverse ^ 2 * (φ ^ 2 * u) := by
        rw [← mul_assoc, golden_inverse_sq_mul_phi_sq, one_mul]
      _ < goldenInverse ^ 2 * (y + φ) := hscaled
  · intro h
    have hscaled := mul_lt_mul_of_pos_left h hφ2
    have hcomm : φ ^ 2 * goldenInverse ^ 2 = 1 := by
      rw [mul_comm, golden_inverse_sq_mul_phi_sq]
    have : φ ^ 2 * u < y + φ := by
      calc
        φ ^ 2 * u < φ ^ 2 * (goldenInverse ^ 2 * (y + φ)) := hscaled
        _ = y + φ := by rw [← mul_assoc, hcomm, one_mul]
    linarith

theorem golden_small_upper_lt_initial_phi_lower :
    1 - goldenInverse / 2 < goldenInitialTubeLows.phiPoint := by
  simp only [goldenInitialTubeLows]
  rw [golden_inverse_eq_sub_one]
  have hφ : (8 : Real) / 5 < φ := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  linarith

theorem golden_small_upper_lt_phi_lower (n : Nat) :
    1 - goldenInverse / 2 < (goldenTubeLows n).phiPoint := by
  cases n with
  | zero => exact golden_small_upper_lt_initial_phi_lower
  | succ n =>
      simp only [goldenTubeLows, goldenTubeStep]
      have hsmall := (golden_tube_lows_bounds n).2.2.2.2.2.2.1
      have hbase := golden_small_upper_lt_initial_phi_lower
      simp only [goldenInitialTubeLows] at hbase
      have ha2 : 0 < goldenInverse ^ 2 := sq_pos_of_pos golden_inverse_pos
      have hscaled := mul_le_mul_of_nonneg_left hsmall ha2.le
      have hid : goldenInverse ^ 2 * (goldenInverse / 2 + φ) =
          (4 * φ - 5) / 2 := by
        rw [golden_inverse_sq, golden_inverse_eq_sub_one]
        nlinarith [Real.goldenRatio_sq]
      have hge : (4 * φ - 5) / 2 ≤
          goldenInverse ^ 2 * ((goldenTubeLows n).small + φ) := by
        rw [← hid]
        nlinarith
      exact hbase.trans_le hge

theorem golden_backward_two_iff (state : GoldenSurvivorState) :
    state ∈ goldenBackwardSurvivor goldenStrictSurvivorSet 2 ↔
      goldenOpenTube 0 state := by
  change state ∈ goldenStrictSurvivorSet ∧
      goldenTransition state ∈ goldenStrictSurvivorSet ∧
      goldenTransition (goldenTransition state) ∈ goldenStrictSurvivorSet ↔ _
  rcases state with ⟨kind, u⟩
  have hφlo : (3 : Real) / 2 < φ := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  have hφhi : φ < 2 := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  cases kind with
  | large =>
      rw [golden_strict_large_iff]
      by_cases hu : u ≤ goldenInverse
      · simp only [goldenTransition, hu, if_pos]
        rw [golden_strict_large_iff]
        by_cases hpu : φ * u ≤ goldenInverse
        · simp only [goldenTransition, hpu, if_pos]
          rw [golden_strict_large_iff]
          simp only [goldenOpenTube, goldenTubeLows, goldenInitialTubeLows]
          rw [golden_threshold_eq, golden_inverse_sq,
            golden_inverse_eq_sub_one] at *
          constructor
          · rintro ⟨h0, h1, h2⟩
            exact Or.inl ⟨by nlinarith [Real.goldenRatio_sq], by
              nlinarith [Real.goldenRatio_sq]⟩
          · intro h
            rcases h with hA | hB | hC
            · exact ⟨
                ⟨by nlinarith [Real.goldenRatio_sq], by nlinarith [Real.goldenRatio_sq]⟩,
                ⟨by nlinarith [Real.goldenRatio_sq], by nlinarith [Real.goldenRatio_sq]⟩,
                ⟨by nlinarith [Real.goldenRatio_sq], by nlinarith [Real.goldenRatio_sq]⟩⟩
            · exfalso
              nlinarith [Real.goldenRatio_sq]
            · exfalso
              nlinarith [Real.goldenRatio_sq]
        · simp only [goldenTransition, hpu, if_false]
          rw [golden_strict_small_iff]
          simp only [goldenOpenTube, goldenTubeLows, goldenInitialTubeLows]
          rw [golden_threshold_eq, golden_inverse_sq,
            golden_inverse_eq_sub_one] at *
          constructor
          · rintro ⟨h0, h1, h2⟩
            exact Or.inr (Or.inl ⟨by nlinarith [Real.goldenRatio_sq], by
              nlinarith [Real.goldenRatio_sq]⟩)
          · intro h
            rcases h with hA | hB | hC
            · exfalso
              nlinarith [Real.goldenRatio_sq]
            · exact ⟨
                ⟨by nlinarith [Real.goldenRatio_sq], by nlinarith [Real.goldenRatio_sq]⟩,
                ⟨by nlinarith [Real.goldenRatio_sq], by nlinarith [Real.goldenRatio_sq]⟩,
                ⟨by nlinarith [Real.goldenRatio_sq], by nlinarith [Real.goldenRatio_sq]⟩⟩
            · exfalso
              nlinarith [Real.goldenRatio_sq]
      · simp only [goldenTransition, hu, if_false]
        rw [golden_strict_small_iff]
        rw [golden_strict_large_iff]
        simp only [goldenOpenTube, goldenTubeLows, goldenInitialTubeLows]
        rw [golden_threshold_eq, golden_inverse_sq,
          golden_inverse_eq_sub_one] at *
        constructor
        · rintro ⟨h0, h1, h2⟩
          exact Or.inr (Or.inr ⟨by nlinarith [Real.goldenRatio_sq], by
            nlinarith [Real.goldenRatio_sq]⟩)
        · intro h
          rcases h with hA | hB | hC
          · exfalso
            nlinarith [Real.goldenRatio_sq]
          · exfalso
            nlinarith [Real.goldenRatio_sq]
          · exact ⟨
              ⟨by nlinarith [Real.goldenRatio_sq], by nlinarith [Real.goldenRatio_sq]⟩,
              ⟨by nlinarith [Real.goldenRatio_sq], by nlinarith [Real.goldenRatio_sq]⟩,
              ⟨by nlinarith [Real.goldenRatio_sq], by nlinarith [Real.goldenRatio_sq]⟩⟩
  | small =>
      rw [golden_strict_small_iff]
      simp only [goldenTransition]
      rw [golden_strict_large_iff]
      by_cases hu : u ≤ goldenInverse
      · simp only [goldenTransition, hu, if_pos]
        rw [golden_strict_large_iff]
        simp only [goldenOpenTube, goldenTubeLows, goldenInitialTubeLows]
        rw [golden_threshold_eq, golden_inverse_sq,
          golden_inverse_eq_sub_one] at *
        constructor
        · rintro ⟨h0, h1, h2⟩
          exact ⟨by nlinarith [Real.goldenRatio_sq], by
            nlinarith [Real.goldenRatio_sq]⟩
        · rintro ⟨hlow, hupp⟩
          exact ⟨
            ⟨by nlinarith [Real.goldenRatio_sq], by nlinarith [Real.goldenRatio_sq]⟩,
            ⟨by nlinarith [Real.goldenRatio_sq], by nlinarith [Real.goldenRatio_sq]⟩,
            ⟨by nlinarith [Real.goldenRatio_sq], by nlinarith [Real.goldenRatio_sq]⟩⟩
      · simp only [goldenTransition, hu, if_false]
        rw [golden_strict_small_iff]
        simp only [goldenOpenTube, goldenTubeLows, goldenInitialTubeLows]
        rw [golden_threshold_eq, golden_inverse_sq,
          golden_inverse_eq_sub_one] at *
        constructor
        · rintro ⟨h0, h1, h2⟩
          exfalso
          nlinarith [Real.goldenRatio_sq]
        · rintro ⟨hlow, hupp⟩
          exfalso
          nlinarith [Real.goldenRatio_sq]

theorem golden_open_tube_preimage (n : Nat) (state : GoldenSurvivorState) :
    state ∈ goldenStrictSurvivorSet ∧
        goldenOpenTube n (goldenTransition state) ↔
      goldenOpenTube (n + 1) state := by
  rcases state with ⟨kind, u⟩
  have hb := golden_tube_lows_bounds n
  have hsep := golden_small_upper_lt_phi_lower n
  have ha := golden_inverse_pos
  have ha1 := golden_inverse_lt_one
  have hhalf := golden_half_le_inverse
  have hthreshold : goldenThreshold = goldenInverse ^ 2 / 2 := golden_threshold_eq
  have hleftCenter : goldenInverse * (φ / 2) = (1 : Real) / 2 := by
    nlinarith [golden_inverse_mul]
  cases kind with
  | large =>
      rw [golden_strict_large_iff]
      by_cases hu : u ≤ goldenInverse
      · simp only [goldenTransition, hu, if_pos, goldenOpenTube,
          goldenTubeLows, goldenTubeStep]
        simp_rw [golden_left_lower_iff, golden_left_upper_iff]
        constructor
        · rintro ⟨hF, hA | hB | hC⟩
          · exfalso
            rw [hthreshold] at hF
            nlinarith [golden_inverse_sq]
          · exact Or.inl ⟨hB.1, by nlinarith [hB.2]⟩
          · exact Or.inr (Or.inl ⟨hC.1, by nlinarith [hleftCenter]⟩)
        · intro h
          rcases h with hA | hB | hC
          · exact ⟨⟨by rw [hthreshold]; nlinarith [hb.2.2.1],
                by nlinarith [ha1, hhalf]⟩,
              Or.inr (Or.inl ⟨hA.1, by nlinarith [hA.2]⟩)⟩
          · exact ⟨⟨by rw [hthreshold]; nlinarith [hb.2.2.2.2.1],
                by nlinarith [ha1, hhalf]⟩,
              Or.inr (Or.inr ⟨hB.1, by nlinarith [hleftCenter, hB.2]⟩)⟩
          · exfalso
            have hnextPhi := (golden_tube_lows_bounds (n + 1)).2.2.2.2.1
            nlinarith
      · simp only [goldenTransition, hu, if_false, goldenOpenTube,
          goldenTubeLows, goldenTubeStep]
        simp_rw [golden_right_lower_iff, golden_right_upper_iff]
        constructor
        · rintro ⟨hF, hD⟩
          exact Or.inr (Or.inr ⟨hD.1, by
            nlinarith [golden_right_branch_center, hD.2]⟩)
        · intro h
          rcases h with hA | hB | hC
          · exfalso
            nlinarith [golden_inverse_lt_phi_half, hA.2]
          · exfalso
            nlinarith [golden_inverse_lt_phi_half, hB.2]
          · refine ⟨⟨?_, hC.2⟩, ⟨hC.1, ?_⟩⟩
            · rw [hthreshold]
              nlinarith [hu, golden_inverse_sq, ha]
            · nlinarith [golden_right_branch_center, hC.2]
  | small =>
      rw [golden_strict_small_iff]
      simp only [goldenTransition, goldenOpenTube, goldenTubeLows, goldenTubeStep]
      constructor
      · rintro ⟨hF, hA | hB | hC⟩
        · exfalso
          nlinarith [hF.1, hA.2]
        · exact hB
        · exfalso
          nlinarith [hF.2, hsep, hC.1]
      · intro h
        exact ⟨⟨by nlinarith [hb.2.2.1], by
            nlinarith [hb.2.2.2.1, golden_inverse_lt_one]⟩,
          Or.inr (Or.inl h)⟩

/-- From depth two onward, the strict backward survivor is exactly the four
nondegenerate open tubes generated by the four inverse branches. -/
theorem golden_backward_survivor_four_tubes (n : Nat) (state : GoldenSurvivorState) :
    state ∈ goldenBackwardSurvivor goldenStrictSurvivorSet (n + 2) ↔
      goldenOpenTube n state := by
  induction n generalizing state with
  | zero => simpa using golden_backward_two_iff state
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega,
        golden_backward_survivor_succ]
      change state ∈ goldenStrictSurvivorSet ∧
          goldenTransition state ∈
            goldenBackwardSurvivor goldenStrictSurvivorSet (n + 2) ↔ _
      rw [ih (goldenTransition state)]
      exact golden_open_tube_preimage n state

example : goldenTransition goldenTailPoint = goldenLargeMidpoint := by
  norm_num only [goldenTransition, goldenTailPoint, goldenLargeMidpoint,
    golden_inverse_half_le_inverse, if_pos]
  congr 1
  nlinarith [golden_inverse_mul]

example : goldenTransition goldenLargeMidpoint = goldenLargePhiPoint := by
  norm_num only [goldenTransition, goldenLargeMidpoint, goldenLargePhiPoint,
    golden_half_le_inverse, if_pos]
  ring

example : goldenTransition goldenLargePhiPoint = goldenSmallMidpoint := by
  norm_num only [goldenTransition, goldenLargePhiPoint, goldenSmallMidpoint,
    not_le.mpr golden_inverse_lt_phi_half, if_false]
  congr 1
  nlinarith [Real.goldenRatio_sq]

example : goldenTransition goldenSmallMidpoint = goldenLargeMidpoint := by
  norm_num only [goldenTransition, goldenSmallMidpoint, goldenLargeMidpoint]

end D5.S0.Tower.Champions.GoldenSurvivorTubes
