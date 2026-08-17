/- GID: D5/S0/Tower/ErgodicBridge/General
   generality: I
   mirror-B: D5/B/S0/Tower/ErgodicBridge/General
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fin-d gap coding identifies d-bonacci grid and ergodic lower-value optima. -/

import D5.S0.Tower.DBonacci.GapAlphabet

/- Library-search audit trail (2026-08-17):
   * Repository search found the typed `Fin d` gap alphabet and separate golden
     and Tribonacci coding arguments, but no reusable bidirectional bridge.
   * Pinned mathlib supplies `Filter.liminf_congr` and `Filter.liminf_nat_add`;
     no third-party result packages the d-bonacci geometry needed by instances.
   * The interface below isolates those geometric obligations per gap letter;
     all orbit, attainable-set, and optimal-value arguments are proved once. -/

namespace D5.S0.Tower.ErgodicBridge.General

/-- Data and geometric laws needed to turn a typed d-bonacci gap coding into an
ergodic optimization problem.  Instance proofs supply one realization uniformly
over the existing `Fin d` gap alphabet. -/
structure DBonacciErgodicBridge (d : Nat) (hd : 2 <= d) where
  State : Type
  stateLetter : State ->
    D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter d
  coordinate : State -> Real
  stateOf : D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter d -> Real -> State
  gapExtent : D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter d -> Real
  transition : State -> State
  stateArm : State -> Real
  unitState : State -> Prop
  gridCarrier : Nat -> Set Real
  gridObservable : Nat -> Real -> Real
  gridCoding : Nat -> Real -> State -> Prop
  firstLevel : Nat
  realizationLevel : Nat
  realizationLevel_valid : firstLevel <= realizationLevel
  stateOf_letter : forall letter u, stateLetter (stateOf letter u) = letter
  stateOf_coordinate : forall letter u, coordinate (stateOf letter u) = u
  state_eta : forall state, stateOf (stateLetter state) (coordinate state) = state
  unitState_iff : forall state,
    unitState state <->
      0 <= coordinate state /\ coordinate state <= gapExtent (stateLetter state)
  coding_unit : forall Q x state, gridCoding Q x state -> unitState state
  coding_observable : forall Q x state, gridCoding Q x state ->
    gridObservable Q x = stateArm state
  coding_transition : forall Q, firstLevel <= Q -> forall x state,
    gridCoding Q x state -> gridCoding (Q + 1) x (transition state)
  coding_exists : forall Q, firstLevel <= Q -> forall x,
    x ∈ gridCarrier Q -> exists state, gridCoding Q x state
  letter_realization : forall
    (letter : D5.S0.Tower.DBonacci.GapAlphabet.DBonacciGapLetter d) (u : Real),
    0 <= u -> u <= gapExtent letter ->
      exists x, x ∈ gridCarrier realizationLevel /\
        gridCoding realizationLevel x (stateOf letter u)

noncomputable def orbitLowerValue {d : Nat} {hd : 2 <= d}
    (bridge : DBonacciErgodicBridge d hd) (state : bridge.State) : Real :=
  Filter.liminf
    (fun n => bridge.stateArm ((bridge.transition^[n]) state)) Filter.atTop

noncomputable def gridLowerValue {d : Nat} {hd : 2 <= d}
    (bridge : DBonacciErgodicBridge d hd) (x : Real) : Real :=
  Filter.liminf (fun Q => bridge.gridObservable Q x) Filter.atTop

theorem grid_coding_iterate {d : Nat} {hd : 2 <= d}
    (bridge : DBonacciErgodicBridge d hd) (Q : Nat) (hQ : bridge.firstLevel <= Q)
    (x : Real) (state : bridge.State) (hcode : bridge.gridCoding Q x state)
    (n : Nat) :
    bridge.gridCoding (Q + n) x ((bridge.transition^[n]) state) := by
  induction n with
  | zero => simpa using hcode
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simpa [Nat.add_assoc] using
        bridge.coding_transition (Q + n) (by omega) x _ ih

theorem grid_observable_eq_orbit_arm {d : Nat} {hd : 2 <= d}
    (bridge : DBonacciErgodicBridge d hd) (Q : Nat) (hQ : bridge.firstLevel <= Q)
    (x : Real) (state : bridge.State) (hcode : bridge.gridCoding Q x state)
    (n : Nat) :
    bridge.gridObservable (Q + n) x =
      bridge.stateArm ((bridge.transition^[n]) state) := by
  exact bridge.coding_observable (Q + n) x _
    (grid_coding_iterate bridge Q hQ x state hcode n)

/-- A typed code intertwining one grid refinement with one transition identifies
the two lower asymptotic observables. -/
theorem ergodic_bridge_of_coding {d : Nat} {hd : 2 <= d}
    (bridge : DBonacciErgodicBridge d hd) (Q : Nat) (hQ : bridge.firstLevel <= Q)
    (x : Real) (state : bridge.State) (hcode : bridge.gridCoding Q x state) :
    gridLowerValue bridge x = orbitLowerValue bridge state := by
  rw [gridLowerValue, ← Filter.liminf_nat_add
    (fun level => bridge.gridObservable level x) Q]
  unfold orbitLowerValue
  apply Filter.liminf_congr
  filter_upwards [] with n
  simpa [Nat.add_comm] using
    grid_observable_eq_orbit_arm bridge Q hQ x state hcode n

/-- Every grid point on an admissible level has a unit-state orbit with the
same lower value. -/
theorem ergodic_bridge {d : Nat} {hd : 2 <= d}
    (bridge : DBonacciErgodicBridge d hd) (Q : Nat) (hQ : bridge.firstLevel <= Q)
    (x : Real) (hx : x ∈ bridge.gridCarrier Q) :
    exists state : bridge.State, bridge.unitState state /\
      gridLowerValue bridge x = orbitLowerValue bridge state := by
  obtain ⟨state, hcode⟩ := bridge.coding_exists Q hQ x hx
  exact ⟨state, bridge.coding_unit Q x state hcode,
    ergodic_bridge_of_coding bridge Q hQ x state hcode⟩

/-- The `Fin d` realization family supplies a grid point for every unit state,
without enumerating a fixed number of gap kinds in the general proof. -/
theorem unit_state_has_grid_realization {d : Nat} {hd : 2 <= d}
    (bridge : DBonacciErgodicBridge d hd) (state : bridge.State)
    (hunit : bridge.unitState state) :
    exists x, x ∈ bridge.gridCarrier bridge.realizationLevel /\
      bridge.gridCoding bridge.realizationLevel x state := by
  have hbounds := (bridge.unitState_iff state).1 hunit
  obtain ⟨x, hx, hcode⟩ := bridge.letter_realization
    (bridge.stateLetter state) (bridge.coordinate state) hbounds.1 hbounds.2
  refine ⟨x, hx, ?_⟩
  simpa only [bridge.state_eta state] using hcode

/-- Conversely, every unit state is attained by a grid point with the same
lower value. -/
theorem ergodic_bridge_reverse {d : Nat} {hd : 2 <= d}
    (bridge : DBonacciErgodicBridge d hd) (state : bridge.State)
    (hunit : bridge.unitState state) :
    exists x, x ∈ bridge.gridCarrier bridge.realizationLevel /\
      gridLowerValue bridge x = orbitLowerValue bridge state := by
  obtain ⟨x, hx, hcode⟩ := unit_state_has_grid_realization bridge state hunit
  exact ⟨x, hx, ergodic_bridge_of_coding bridge bridge.realizationLevel
    bridge.realizationLevel_valid x state hcode⟩

def gridLowerValues {d : Nat} {hd : 2 <= d}
    (bridge : DBonacciErgodicBridge d hd) : Set Real :=
  {value | exists Q : Nat, bridge.firstLevel <= Q /\
    exists x, x ∈ bridge.gridCarrier Q /\ value = gridLowerValue bridge x}

def ergodicLowerValues {d : Nat} {hd : 2 <= d}
    (bridge : DBonacciErgodicBridge d hd) : Set Real :=
  {value | exists state : bridge.State,
    bridge.unitState state /\ value = orbitLowerValue bridge state}

/-- The grid and orbit problems attain exactly the same lower values. -/
theorem lower_value_sets_eq {d : Nat} {hd : 2 <= d}
    (bridge : DBonacciErgodicBridge d hd) :
    gridLowerValues bridge = ergodicLowerValues bridge := by
  ext value
  constructor
  · rintro ⟨Q, hQ, x, hx, hvalue⟩
    obtain ⟨state, hunit, hbridge⟩ := ergodic_bridge bridge Q hQ x hx
    exact ⟨state, hunit, hvalue.trans hbridge⟩
  · rintro ⟨state, hunit, hvalue⟩
    obtain ⟨x, hx, hbridge⟩ := ergodic_bridge_reverse bridge state hunit
    exact ⟨bridge.realizationLevel, bridge.realizationLevel_valid,
      x, hx, hvalue.trans hbridge.symm⟩

noncomputable def gridOptimalValue {d : Nat} {hd : 2 <= d}
    (bridge : DBonacciErgodicBridge d hd) : Real :=
  sSup (gridLowerValues bridge)

noncomputable def ergodicOptimalValue {d : Nat} {hd : 2 <= d}
    (bridge : DBonacciErgodicBridge d hd) : Real :=
  sSup (ergodicLowerValues bridge)

/-- Bidirectional typed coding identifies the d-bonacci champion objective
with the ergodic maximin objective. -/
theorem optimal_value_eq_ergodic_optimal_value {d : Nat} {hd : 2 <= d}
    (bridge : DBonacciErgodicBridge d hd) :
    gridOptimalValue bridge = ergodicOptimalValue bridge := by
  rw [gridOptimalValue, ergodicOptimalValue, lower_value_sets_eq bridge]

end D5.S0.Tower.ErgodicBridge.General
