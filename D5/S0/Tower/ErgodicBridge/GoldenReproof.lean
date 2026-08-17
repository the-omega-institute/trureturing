/- GID: D5/S0/Tower/ErgodicBridge/GoldenReproof
   generality: I
   mirror-B: D5/B/S0/Tower/ErgodicBridge/GoldenReproof
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The frozen golden optimum is reproved by the general Fin-d ergodic bridge. -/

import D5.S0.Tower.ErgodicBridge.General
import D5.S0.Tower.ErgodicBridge.Golden

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen golden coding geometry and the general
     Fin-d bridge, but no independent substitution of the former into the latter.
   * The proof below reuses only the frozen public geometry laws, not its final
     optimal-value theorem, and identifies the pre-existing value-set names
     with the general bridge sets. -/

namespace D5.S0.Tower.ErgodicBridge.GoldenReproof

def goldenStateLetter
    (state : D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState) :
    D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter 2 :=
  match state.kind with
  | .large => ⟨0, by omega⟩
  | .small => ⟨1, by omega⟩

def goldenStateOf
    (letter : D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter 2) (u : Real) :
    D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState :=
  if letter.1 = 0 then ⟨.large, u⟩ else ⟨.small, u⟩

/-- The frozen golden geometry discharges the general bridge laws at `d = 2`. -/
noncomputable def goldenBridgeData :
    D5.S0.Tower.ErgodicBridge.General.DBonacciErgodicBridge 2 (by omega) where
  State := D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState
  stateLetter := goldenStateLetter
  coordinate := fun state => state.coordinate
  stateOf := goldenStateOf
  gapExtent := fun _ => 1
  transition := D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenTransition
  stateArm := D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenStateArm
  unitState := D5.S0.Tower.ErgodicBridge.Golden.GoldenUnitState
  gridCarrier := D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenNameHull
  gridObservable := D5.S0.Tower.MetricGeometry.GoldenSurvivor.goldenSurvivor
  gridCoding := D5.S0.Tower.ErgodicBridge.Golden.GoldenGridCoding
  firstLevel := 2
  realizationLevel := 2
  realizationLevel_valid := by omega
  stateOf_letter := by intro letter u; fin_cases letter <;> rfl
  stateOf_coordinate := by intro letter u; fin_cases letter <;> rfl
  state_eta := by intro state; rcases state with ⟨kind, u⟩; cases kind <;> rfl
  unitState_iff := by intro state; rcases state with ⟨kind, u⟩; cases kind <;> rfl
  coding_unit := by intro Q x state hcode; exact hcode.1
  coding_observable :=
    D5.S0.Tower.ErgodicBridge.Golden.golden_survivor_eq_state_arm
  coding_transition :=
    D5.S0.Tower.ErgodicBridge.Golden.golden_grid_coding_transition
  coding_exists := by
    intro Q _ x
    exact D5.S0.Tower.ErgodicBridge.Golden.golden_grid_coding_exists_of_mem_hull Q x
  letter_realization := by
    intro letter u hu0 hu1
    fin_cases letter
    · exact
        D5.S0.Tower.ErgodicBridge.Golden.golden_unit_state_has_grid_realization
          ⟨.large, u⟩ ⟨hu0, hu1⟩
    · exact
        D5.S0.Tower.ErgodicBridge.Golden.golden_unit_state_has_grid_realization
          ⟨.small, u⟩ ⟨hu0, hu1⟩

/-- The pre-existing golden optimum equality follows from the general `Fin 2`
bridge, independently of the frozen theorem proving the same formula. -/
theorem golden_general_bridge_optimal_value_reproved :
    D5.S0.Tower.ErgodicBridge.Golden.goldenGridOptimalValue =
      D5.S0.Tower.ErgodicBridge.Golden.goldenErgodicOptimalValue := by
  have hgrid :
      D5.S0.Tower.ErgodicBridge.Golden.goldenGridLowerValues =
        D5.S0.Tower.ErgodicBridge.General.gridLowerValues goldenBridgeData := by
    ext value
    constructor
    · rintro ⟨Q, hQ, x, hx, hvalue⟩
      exact ⟨Q, hQ, x, hx, by
        simpa [D5.S0.Tower.ErgodicBridge.General.gridLowerValue,
          goldenBridgeData] using hvalue⟩
    · rintro ⟨Q, hQ, x, hx, hvalue⟩
      exact ⟨Q, hQ, x, hx, by
        simpa [D5.S0.Tower.ErgodicBridge.General.gridLowerValue,
          goldenBridgeData] using hvalue⟩
  have hergodic :
      D5.S0.Tower.ErgodicBridge.Golden.goldenErgodicLowerValues =
        D5.S0.Tower.ErgodicBridge.General.ergodicLowerValues goldenBridgeData := by
    ext value
    constructor
    · rintro ⟨state, hunit, hvalue⟩
      exact ⟨state, hunit, by
        simpa [D5.S0.Tower.ErgodicBridge.General.orbitLowerValue,
          goldenBridgeData,
          D5.S0.Tower.ErgodicBridge.Golden.goldenOrbitLowerValue] using hvalue⟩
    · rintro ⟨state, hunit, hvalue⟩
      exact ⟨state, hunit, by
        simpa [D5.S0.Tower.ErgodicBridge.General.orbitLowerValue,
          goldenBridgeData,
          D5.S0.Tower.ErgodicBridge.Golden.goldenOrbitLowerValue] using hvalue⟩
  rw [D5.S0.Tower.ErgodicBridge.Golden.goldenGridOptimalValue,
    D5.S0.Tower.ErgodicBridge.Golden.goldenErgodicOptimalValue,
    hgrid, hergodic]
  simpa [D5.S0.Tower.ErgodicBridge.General.gridOptimalValue,
    D5.S0.Tower.ErgodicBridge.General.ergodicOptimalValue] using
      D5.S0.Tower.ErgodicBridge.General.optimal_value_eq_ergodic_optimal_value
        goldenBridgeData

end D5.S0.Tower.ErgodicBridge.GoldenReproof
