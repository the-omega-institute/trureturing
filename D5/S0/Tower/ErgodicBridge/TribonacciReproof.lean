/- GID: D5/S0/Tower/ErgodicBridge/TribonacciReproof
   generality: I
   mirror-B: D5/B/S0/Tower/ErgodicBridge/TribonacciReproof
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The frozen Tribonacci optimum is reproved by the general Fin-d ergodic bridge. -/

import D5.S0.Tower.ErgodicBridge.General
import D5.S0.Tower.ErgodicBridge.Tribonacci

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen Tribonacci coding geometry and the
     general Fin-d bridge, but no substitution of the former into the latter.
   * The proof below reuses only the frozen public geometry laws, not its final
     optimal-value theorem, and identifies the pre-existing value-set names
     with the general bridge sets. -/

namespace D5.S0.Tower.ErgodicBridge.TribonacciReproof

def tribonacciStateLetter
    (state :
      D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicState) :
    D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter 3 :=
  match state.kind with
  | .small => ⟨0, by omega⟩
  | .combined => ⟨1, by omega⟩
  | .large => ⟨2, by omega⟩

def tribonacciGapOfLetter
    (letter : D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter 3) :
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicGap :=
  if letter.1 = 0 then .small else if letter.1 = 1 then .combined else .large

def tribonacciStateOf
    (letter : D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter 3) (u : Real) :
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicState :=
  ⟨tribonacciGapOfLetter letter, u⟩

noncomputable def tribonacciLetterExtent
    (letter : D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter 3) : Real :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength
    (tribonacciGapOfLetter letter)

/-- The frozen Tribonacci geometry discharges the general bridge laws at `d = 3`. -/
noncomputable def tribonacciBridgeData :
    D5.S0.Tower.ErgodicBridge.General.DBonacciErgodicBridge 3 (by omega) where
  State :=
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicState
  stateLetter := tribonacciStateLetter
  coordinate := fun state => state.coordinate
  stateOf := tribonacciStateOf
  gapExtent := tribonacciLetterExtent
  transition :=
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition
  stateArm :=
    D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin.tribonacciPeriodicStateArm
  unitState := D5.S0.Tower.ErgodicBridge.Tribonacci.TribonacciUnitState
  gridCarrier := D5.S0.Tower.Tribonacci.Survivor.tribonacciNameHull
  gridObservable := D5.S0.Tower.Tribonacci.Survivor.tribonacciSurvivor
  gridCoding := D5.S0.Tower.ErgodicBridge.Tribonacci.TribonacciGridCoding
  firstLevel := 0
  realizationLevel := 3
  realizationLevel_valid := by omega
  stateOf_letter := by intro letter u; fin_cases letter <;> rfl
  stateOf_coordinate := by intro letter u; rfl
  state_eta := by intro state; rcases state with ⟨kind, u⟩; cases kind <;> rfl
  unitState_iff := by intro state; rcases state with ⟨kind, u⟩; cases kind <;> rfl
  coding_unit := by intro Q x state hcode; exact hcode.1
  coding_observable :=
    D5.S0.Tower.ErgodicBridge.Tribonacci.tribonacci_survivor_eq_state_arm
  coding_transition := by
    intro Q _ x state
    exact D5.S0.Tower.ErgodicBridge.Tribonacci.tribonacci_grid_coding_transition
      Q x state
  coding_exists := by
    intro Q _ x
    exact D5.S0.Tower.ErgodicBridge.Tribonacci.tribonacci_grid_coding_exists_of_mem_hull
      Q x
  letter_realization := by
    intro letter u hu0 hu1
    fin_cases letter
    · exact
        D5.S0.Tower.ErgodicBridge.Tribonacci.tribonacci_unit_state_has_grid_realization
          ⟨.small, u⟩ ⟨hu0, hu1⟩
    · exact
        D5.S0.Tower.ErgodicBridge.Tribonacci.tribonacci_unit_state_has_grid_realization
          ⟨.combined, u⟩ ⟨hu0, hu1⟩
    · exact
        D5.S0.Tower.ErgodicBridge.Tribonacci.tribonacci_unit_state_has_grid_realization
          ⟨.large, u⟩ ⟨hu0, hu1⟩

theorem tribonacci_grid_lower_values_eq_general :
    D5.S0.Tower.ErgodicBridge.Tribonacci.tribonacciGridLowerValues =
      D5.S0.Tower.ErgodicBridge.General.gridLowerValues tribonacciBridgeData := by
  ext value
  constructor
  · rintro ⟨Q, x, hx, hvalue⟩
    exact ⟨Q, by change 0 <= Q; omega, x, hx, by
      simpa [D5.S0.Tower.ErgodicBridge.General.gridLowerValue,
        tribonacciBridgeData] using hvalue⟩
  · rintro ⟨Q, _, x, hx, hvalue⟩
    exact ⟨Q, x, hx, by
      simpa [D5.S0.Tower.ErgodicBridge.General.gridLowerValue,
        tribonacciBridgeData] using hvalue⟩

theorem tribonacci_ergodic_lower_values_eq_general :
    D5.S0.Tower.ErgodicBridge.Tribonacci.tribonacciErgodicLowerValues =
      D5.S0.Tower.ErgodicBridge.General.ergodicLowerValues tribonacciBridgeData := by
  ext value
  constructor
  · rintro ⟨state, hunit, hvalue⟩
    exact ⟨state, hunit, by
      simpa [D5.S0.Tower.ErgodicBridge.General.orbitLowerValue,
        tribonacciBridgeData,
        D5.S0.Tower.ErgodicBridge.Tribonacci.tribonacciOrbitLowerValue] using hvalue⟩
  · rintro ⟨state, hunit, hvalue⟩
    exact ⟨state, hunit, by
      simpa [D5.S0.Tower.ErgodicBridge.General.orbitLowerValue,
        tribonacciBridgeData,
        D5.S0.Tower.ErgodicBridge.Tribonacci.tribonacciOrbitLowerValue] using hvalue⟩

/-- The pre-existing Tribonacci optimum equality follows from the general
`Fin 3` bridge, independently of the frozen theorem proving the same formula. -/
theorem tribonacci_general_bridge_optimal_value_reproved :
    D5.S0.Tower.ErgodicBridge.Tribonacci.tribonacciGridOptimalValue =
      D5.S0.Tower.ErgodicBridge.Tribonacci.tribonacciErgodicOptimalValue := by
  rw [D5.S0.Tower.ErgodicBridge.Tribonacci.tribonacciGridOptimalValue,
    D5.S0.Tower.ErgodicBridge.Tribonacci.tribonacciErgodicOptimalValue,
    tribonacci_grid_lower_values_eq_general,
    tribonacci_ergodic_lower_values_eq_general]
  simpa [D5.S0.Tower.ErgodicBridge.General.gridOptimalValue,
    D5.S0.Tower.ErgodicBridge.General.ergodicOptimalValue] using
      D5.S0.Tower.ErgodicBridge.General.optimal_value_eq_ergodic_optimal_value
        tribonacciBridgeData

end D5.S0.Tower.ErgodicBridge.TribonacciReproof
