/- GID: D5/S0/Tower/ErgodicBridge/Tribonacci
   generality: I
   mirror-B: D5/B/S0/Tower/ErgodicBridge/Tribonacci
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Tribonacci name-grid liminf equals the lower arm value of its three-gap orbit. -/

import D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin
import D5.S0.Tower.Tribonacci.ChampionOrbit

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen three-gap substitution, its five-edge
     expanding transition, exact survivor arms, and periodic maximin, but no
     bidirectional coding between arbitrary grid points and transition states.
   * Pinned mathlib supplies `Filter.liminf_congr` and `Filter.liminf_nat_add`;
     neither contains geometry specific to Tribonacci-name grids.
   * The in-flight golden bridge supplied the reduction architecture.  The
     three-gap transition and all three realization cases are proved here. -/

/- The carrier below is the internal name-grid hull.  Its omitted right terminal
   point has a one-sided terminal gap, not a state of the two-ended expanding map. -/

namespace D5.S0.Tower.ErgodicBridge.Tribonacci

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant
local notation "State" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicState
local notation "gapLength" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength
local notation "transition" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition
local notation "stateArm" =>
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicMaximin.tribonacciPeriodicStateArm

/-- The natural state interval depends on the current gap letter. -/
def TribonacciUnitState (state : State) : Prop :=
  0 <= state.coordinate /\ state.coordinate <= gapLength state.kind

/-- A state codes the two normalized arms of the adjacent grid gap containing `x`. -/
def TribonacciGridCoding (Q : Nat) (x : Real) (state : State) : Prop :=
  TribonacciUnitState state /\
    D5.S0.Tower.Tribonacci.ChampionOrbit.IsTribonacciOrbitGap Q x
      state.coordinate (gapLength state.kind - state.coordinate)

/-- Lower arm value along the expanding three-gap orbit. -/
noncomputable def tribonacciOrbitLowerValue (state : State) : Real :=
  Filter.liminf (fun n => stateArm ((transition^[n]) state)) Filter.atTop

theorem tribonacci_inverse_eq_quadratic : t⁻¹ = t ^ 2 - t - 1 :=
  D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration.tribonacci_inverse_polynomial

theorem tribonacci_inverse_scale (Q : Nat) :
    t⁻¹ * t ^ (-(Q : Int)) = t ^ (-((Q + 1 : Nat) : Int)) := by
  simpa [zpow_neg] using
    D5.S0.Tower.Tribonacci.Gaps.tribonacci_zpow_shift_one Q

theorem tribonacci_mul_combined_sub_one : t * (t - 1) - 1 = t⁻¹ := by
  rw [tribonacci_inverse_eq_quadratic]
  ring

theorem tribonacci_survivor_eq_state_arm (Q : Nat) (x : Real) (state : State)
    (hcode : TribonacciGridCoding Q x state) :
    D5.S0.Tower.Tribonacci.Survivor.tribonacciSurvivor Q x = stateArm state := by
  rcases hcode with ⟨⟨hcoordinate0, hcoordinate1⟩, hgap⟩
  apply D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacciSurvivor_eq_of_orbit_gap
      (hgap := hgap)
  · exact hcoordinate0
  · exact sub_nonneg.mpr hcoordinate1
  · exact min_le_left _ _
  · exact min_le_right _ _
  · by_cases hleft : state.coordinate <= gapLength state.kind - state.coordinate
    · left
      exact min_eq_left hleft
    · right
      exact min_eq_right (le_of_not_ge hleft)

theorem tribonacci_gap_eq_periodic_length (Q : Nat)
    (i : Fin (D5.S0.Tower.Tribonacci.Names.tribonacci (Q + 2) - 1)) :
    ∃ kind : D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicGap,
      D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
            (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight Q i) -
          D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
            (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft Q i) =
        gapLength kind * t ^ (-(Q : Int)) := by
  rcases D5.S0.Tower.Tribonacci.Gaps.consecutive_nameValue_gap Q i with
      hlarge | hsmall | hcombined
  · refine ⟨.large, ?_⟩
    simpa [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength,
      D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft,
      D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight] using hlarge
  · refine ⟨.small, ?_⟩
    rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength,
      tribonacci_inverse_scale Q]
    simpa [D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft,
      D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight] using hsmall
  · refine ⟨.combined, ?_⟩
    rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength,
      D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_combined_scale Q]
    simpa [D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft,
      D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight] using hcombined

theorem tribonacci_grid_coding_in_gap (Q : Nat) (x : Real)
    (i : Fin (D5.S0.Tower.Tribonacci.Names.tribonacci (Q + 2) - 1))
    (kind : D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicGap)
    (hx : x ∈ Set.Icc
      (D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
        (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft Q i))
      (D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
        (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight Q i)))
    (hgap :
      D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
            (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight Q i) -
          D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
            (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft Q i) =
        gapLength kind * t ^ (-(Q : Int))) :
    ∃ state : State, state.kind = kind /\ TribonacciGridCoding Q x state := by
  let a := D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
    (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft Q i)
  let b := D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
    (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight Q i)
  let scale := t ^ (-(Q : Int))
  let u := (x - a) / scale
  change a <= x /\ x <= b at hx
  have hscalePos : 0 < scale := zpow_pos
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos _
  have hu0 : 0 <= u := div_nonneg (sub_nonneg.mpr hx.1) hscalePos.le
  have hu1 : u <= gapLength kind := by
    apply (div_le_iff₀ hscalePos).2
    change x - a <= gapLength kind * scale
    rw [← hgap]
    linarith
  have hleft : x - a = u * scale := by
    dsimp [u]
    field_simp
  have hright : b - x = (gapLength kind - u) * scale := by
    calc
      b - x = (b - a) - (x - a) := by ring
      _ = gapLength kind * scale - u * scale := by rw [hgap, hleft]
      _ = (gapLength kind - u) * scale := by ring
  refine ⟨⟨kind, u⟩, rfl, ⟨⟨hu0, hu1⟩, i, ?_, ?_⟩⟩
  · exact hleft
  · exact hright

/-- Every point in an internal Tribonacci-name hull has a typed gap code. -/
theorem tribonacci_grid_coding_exists_of_mem_hull (Q : Nat) (x : Real)
    (hx : x ∈ D5.S0.Tower.Tribonacci.Survivor.tribonacciNameHull Q) :
    ∃ state : State, TribonacciGridCoding Q x state := by
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  obtain ⟨kind, hgap⟩ := tribonacci_gap_eq_periodic_length Q i
  obtain ⟨state, _, hcode⟩ :=
    tribonacci_grid_coding_in_gap Q x i kind hxi hgap
  exact ⟨state, hcode⟩

theorem tribonacci_state_realized_in_gap (Q : Nat)
    (i : Fin (D5.S0.Tower.Tribonacci.Names.tribonacci (Q + 2) - 1))
    (kind : D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.TribonacciPeriodicGap)
    (u : Real) (hu0 : 0 <= u) (hu1 : u <= gapLength kind)
    (hgap :
      D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
            (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight Q i) -
          D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
            (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft Q i) =
        gapLength kind * t ^ (-(Q : Int))) :
    ∃ x ∈ D5.S0.Tower.Tribonacci.Survivor.tribonacciNameHull Q,
      TribonacciGridCoding Q x ⟨kind, u⟩ := by
  let a := D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
    (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft Q i)
  let b := D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
    (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight Q i)
  let scale := t ^ (-(Q : Int))
  let x := a + u * scale
  have hscalePos : 0 < scale := zpow_pos
    D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos _
  have hleft : a <= x := by
    dsimp [x]
    nlinarith [mul_nonneg hu0 hscalePos.le]
  have hright : x <= b := by
    have hmul := mul_le_mul_of_nonneg_right hu1 hscalePos.le
    rw [← hgap] at hmul
    dsimp [x]
    linarith
  refine ⟨x, Set.mem_iUnion.mpr ⟨i, ⟨hleft, hright⟩⟩,
    ⟨⟨hu0, hu1⟩, i, ?_, ?_⟩⟩
  · change x - a = u * scale
    dsimp [x]
    ring
  · change b - x = (gapLength kind - u) * scale
    calc
      b - x = (b - a) - u * scale := by dsimp [x]; ring
      _ = gapLength kind * scale - u * scale := by rw [hgap]
      _ = (gapLength kind - u) * scale := by ring

theorem tribonacci_large_state_realized_in_gap (Q : Nat)
    (i : Fin (D5.S0.Tower.Tribonacci.Names.tribonacci (Q + 2) - 1))
    (u : Real) (hu0 : 0 <= u) (hu1 : u <= 1)
    (hlarge :
      D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
            (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight Q i) -
          D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
            (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft Q i) =
        t ^ (-(Q : Int))) :
    ∃ x ∈ D5.S0.Tower.Tribonacci.Survivor.tribonacciNameHull Q,
      TribonacciGridCoding Q x ⟨.large, u⟩ := by
  apply tribonacci_state_realized_in_gap Q i .large u hu0
  · simpa [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength]
      using hu1
  · simpa [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength]
      using hlarge

theorem tribonacci_small_state_realized_in_gap (Q : Nat)
    (i : Fin (D5.S0.Tower.Tribonacci.Names.tribonacci (Q + 2) - 1))
    (u : Real) (hu0 : 0 <= u) (hu1 : u <= t⁻¹)
    (hsmall :
      D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
            (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight Q i) -
          D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
            (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft Q i) =
        t ^ (-((Q + 1 : Nat) : Int))) :
    ∃ x ∈ D5.S0.Tower.Tribonacci.Survivor.tribonacciNameHull Q,
      TribonacciGridCoding Q x ⟨.small, u⟩ := by
  apply tribonacci_state_realized_in_gap Q i .small u hu0
  · simpa [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength]
      using hu1
  · rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength,
      tribonacci_inverse_scale Q]
    exact hsmall

theorem tribonacci_combined_state_realized_in_gap (Q : Nat)
    (i : Fin (D5.S0.Tower.Tribonacci.Names.tribonacci (Q + 2) - 1))
    (u : Real) (hu0 : 0 <= u) (hu1 : u <= t - 1)
    (hcombined :
      D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
            (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight Q i) -
          D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
            (D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft Q i) =
        t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int))) :
    ∃ x ∈ D5.S0.Tower.Tribonacci.Survivor.tribonacciNameHull Q,
      TribonacciGridCoding Q x ⟨.combined, u⟩ := by
  apply tribonacci_state_realized_in_gap Q i .combined u hu0
  · simpa [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength]
      using hu1
  · rw [D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicGapLength,
      D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_combined_scale Q]
    exact hcombined

theorem tribonacci_inserted_empty_positions (Q : Nat)
    (i : Fin (D5.S0.Tower.Tribonacci.Names.tribonacci (Q + 2) - 1))
    (hempty : D5.S0.Tower.Tribonacci.Substitution.insertedNameIndices Q i = ∅) :
    (D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
        (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)).1 + 1 =
      (D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
        (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i)).1 := by
  have hlt := D5.S0.Tower.Tribonacci.Substitution.levelEmbedding_strictMono Q
    (D5.S0.Tower.Tribonacci.Substitution.gapLeft_lt_gapRight Q i)
  have hcard :
      (D5.S0.Tower.Tribonacci.Substitution.insertedNameIndices Q i).card = 0 := by
    rw [hempty]
    simp
  rw [D5.S0.Tower.Tribonacci.Substitution.insertedNameIndices, Fin.card_Ioo] at hcard
  change (D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
      (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)).1 <
    (D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
      (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i)).1 at hlt
  omega

theorem tribonacci_transition_unit (state : State)
    (hunit : TribonacciUnitState state) :
    TribonacciUnitState (transition state) := by
  rcases state with ⟨kind, u⟩
  rcases hunit with ⟨hu0, hu1⟩
  cases kind with
  | large =>
      change u <= 1 at hu1
      simp only [
        D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition]
      split_ifs with hbranch
      · change 0 <= t * u /\ t * u <= 1
        constructor
        · exact mul_nonneg D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos.le hu0
        · have hmul := mul_le_mul_of_nonneg_left hbranch
            D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos.le
          rw [mul_inv_cancel₀
            D5.S0.Tower.Tribonacci.Values.tribonacciConstant_ne_zero] at hmul
          exact hmul
      · change 0 <= t * u - 1 /\ t * u - 1 <= t - 1
        constructor
        · have hmul := mul_lt_mul_of_pos_left (lt_of_not_ge hbranch)
            D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos
          rw [mul_inv_cancel₀
            D5.S0.Tower.Tribonacci.Values.tribonacciConstant_ne_zero] at hmul
          linarith
        · have hmul := mul_le_mul_of_nonneg_left hu1
            D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos.le
          linarith
  | small =>
      change u <= t⁻¹ at hu1
      change 0 <= t * u /\ t * u <= 1
      constructor
      · exact mul_nonneg D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos.le hu0
      · have hmul := mul_le_mul_of_nonneg_left hu1
          D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos.le
        rw [mul_inv_cancel₀
          D5.S0.Tower.Tribonacci.Values.tribonacciConstant_ne_zero] at hmul
        exact hmul
  | combined =>
      change u <= t - 1 at hu1
      simp only [
        D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition]
      split_ifs with hbranch
      · change 0 <= t * u /\ t * u <= 1
        constructor
        · exact mul_nonneg D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos.le hu0
        · have hmul := mul_le_mul_of_nonneg_left hbranch
            D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos.le
          rw [mul_inv_cancel₀
            D5.S0.Tower.Tribonacci.Values.tribonacciConstant_ne_zero] at hmul
          exact hmul
      · change 0 <= t * u - 1 /\ t * u - 1 <= t⁻¹
        constructor
        · have hmul := mul_lt_mul_of_pos_left (lt_of_not_ge hbranch)
            D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos
          rw [mul_inv_cancel₀
            D5.S0.Tower.Tribonacci.Values.tribonacciConstant_ne_zero] at hmul
          linarith
        · have hmul := mul_le_mul_of_nonneg_left hu1
            D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos.le
          calc
            t * u - 1 <= t * (t - 1) - 1 := sub_le_sub_right hmul 1
            _ = t⁻¹ := tribonacci_mul_combined_sub_one

theorem tribonacci_grid_coding_transition (Q : Nat) (x : Real) (state : State)
    (hcode : TribonacciGridCoding Q x state) :
    TribonacciGridCoding (Q + 1) x (transition state) := by
  rcases state with ⟨kind, u⟩
  rcases hcode with ⟨hunit, hgap⟩
  cases kind with
  | small =>
      rcases hunit with ⟨hu0, hu1⟩
      rcases hgap with ⟨i, hleft, hright⟩
      change u <= t⁻¹ at hu1
      change x - D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
          (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i) =
        u * t ^ (-(Q : Int)) at hleft
      change D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
          (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i) - x =
        (t⁻¹ - u) * t ^ (-(Q : Int)) at hright
      have hsmall :
          D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i) -
              D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i) =
            t ^ (-((Q + 1 : Nat) : Int)) := by
        calc
          _ = (D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i) - x) +
              (x - D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)) := by ring
          _ = ((t⁻¹ - u) + u) * t ^ (-(Q : Int)) := by rw [hleft, hright]; ring
          _ = t⁻¹ * t ^ (-(Q : Int)) := by ring
          _ = t ^ (-((Q + 1 : Nat) : Int)) := tribonacci_inverse_scale Q
      obtain ⟨hempty, _⟩ :=
        (D5.S0.Tower.Tribonacci.Substitution.tribonacci_gap_substitution Q i).1 hsmall
      have hpositions := tribonacci_inserted_empty_positions Q i hempty
      let next : Fin (D5.S0.Tower.Tribonacci.Names.tribonacci ((Q + 1) + 2) - 1) :=
        ⟨(D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
            (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)).1, by
          change (D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
              (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)).1 <
            D5.S0.Tower.Tribonacci.Names.tribonacci (Q + 3) - 1
          have hrightBound := (D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
            (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i)).2
          omega⟩
      have hnextLeft :
          D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft (Q + 1) next =
            D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
              (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i) := by
        apply Fin.ext
        rfl
      have hnextRight :
          D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight (Q + 1) next =
            D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
              (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i) := by
        apply Fin.ext
        simpa [next, D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight] using
          hpositions
      change TribonacciGridCoding (Q + 1) x (⟨.large, t * u⟩ : State)
      refine ⟨by simpa only [
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition]
          using tribonacci_transition_unit (⟨.small, u⟩ : State) ⟨hu0, hu1⟩,
        next, ?_, ?_⟩
      · rw [hnextLeft, D5.S0.Tower.Tribonacci.Substitution.levelEmbedding_value]
        calc
          x - D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i) =
              u * t ^ (-(Q : Int)) := hleft
          _ = (t * u) * t ^ (-((Q + 1 : Nat) : Int)) := by
            rw [D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_scale_succ Q]
            ring
      · rw [hnextRight, D5.S0.Tower.Tribonacci.Substitution.levelEmbedding_value]
        change D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
              (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i) - x =
            (1 - t * u) * t ^ (-((Q + 1 : Nat) : Int))
        rw [hright, D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_scale_succ Q]
        field_simp [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_ne_zero]
  | combined =>
      rcases hunit with ⟨hu0, hu1⟩
      rcases hgap with ⟨i, hleft, hright⟩
      change u <= t - 1 at hu1
      change x - D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
          (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i) =
        u * t ^ (-(Q : Int)) at hleft
      change D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
          (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i) - x =
        (t - 1 - u) * t ^ (-(Q : Int)) at hright
      have hcombined :
          D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i) -
              D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i) =
            t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int)) := by
        calc
          _ = (D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i) - x) +
              (x - D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)) := by ring
          _ = ((t - 1 - u) + u) * t ^ (-(Q : Int)) := by rw [hleft, hright]; ring
          _ = (t - 1) * t ^ (-(Q : Int)) := by ring
          _ = _ := D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_combined_scale Q
      obtain ⟨j, hset, hjleft, hjright⟩ :=
        (D5.S0.Tower.Tribonacci.Substitution.tribonacci_gap_substitution Q i).2.2 hcombined
      have hpositions :=
        D5.S0.Tower.Tribonacci.ChampionOrbit.inserted_singleton_positions Q i j hset
      by_cases hbranch : u <= t⁻¹
      · let next : Fin
            (D5.S0.Tower.Tribonacci.Names.tribonacci ((Q + 1) + 2) - 1) :=
          ⟨(D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
              (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)).1, by
            change (D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
                (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)).1 <
              D5.S0.Tower.Tribonacci.Names.tribonacci (Q + 3) - 1
            have hjBound := j.2
            omega⟩
        have hnextLeft :
            D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft (Q + 1) next =
              D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
                (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i) := by
          apply Fin.ext
          rfl
        have hnextRight :
            D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight (Q + 1) next = j := by
          apply Fin.ext
          exact hpositions.1
        simp only [
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
          if_pos hbranch]
        refine ⟨by simpa [
            D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
            hbranch] using
              tribonacci_transition_unit (⟨.combined, u⟩ : State) ⟨hu0, hu1⟩,
          next, ?_, ?_⟩
        · rw [hnextLeft, D5.S0.Tower.Tribonacci.Substitution.levelEmbedding_value]
          calc
            x - D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                  (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i) =
                u * t ^ (-(Q : Int)) := hleft
            _ = (t * u) * t ^ (-((Q + 1 : Nat) : Int)) := by
              rw [D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_scale_succ Q]
              ring
        · rw [hnextRight]
          calc
            D5.S0.Tower.Tribonacci.Values.indexedNameValue (Q + 1) j - x =
                (D5.S0.Tower.Tribonacci.Values.indexedNameValue (Q + 1) j -
                    D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                      (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)) -
                  (x - D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                    (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)) := by ring
            _ = t ^ (-((Q + 1 : Nat) : Int)) - u * t ^ (-(Q : Int)) := by
              rw [hjleft, hleft]
            _ = (1 - t * u) * t ^ (-((Q + 1 : Nat) : Int)) := by
              rw [D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_scale_succ Q]
              ring
      · let next : Fin
            (D5.S0.Tower.Tribonacci.Names.tribonacci ((Q + 1) + 2) - 1) :=
          ⟨j.1, by
            change j.1 < D5.S0.Tower.Tribonacci.Names.tribonacci (Q + 3) - 1
            have hrightBound := (D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
              (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i)).2
            omega⟩
        have hnextLeft :
            D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft (Q + 1) next = j := by
          apply Fin.ext
          rfl
        have hnextRight :
            D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight (Q + 1) next =
              D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
                (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i) := by
          apply Fin.ext
          exact hpositions.2
        simp only [
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
          if_neg hbranch]
        refine ⟨by simpa [
            D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
            hbranch] using
              tribonacci_transition_unit (⟨.combined, u⟩ : State) ⟨hu0, hu1⟩,
          next, ?_, ?_⟩
        · rw [hnextLeft]
          calc
            x - D5.S0.Tower.Tribonacci.Values.indexedNameValue (Q + 1) j =
                (x - D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                    (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)) -
                  (D5.S0.Tower.Tribonacci.Values.indexedNameValue (Q + 1) j -
                    D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                      (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)) := by ring
            _ = u * t ^ (-(Q : Int)) - t ^ (-((Q + 1 : Nat) : Int)) := by
              rw [hleft, hjleft]
            _ = (t * u - 1) * t ^ (-((Q + 1 : Nat) : Int)) := by
              rw [D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_scale_succ Q]
              ring
        · rw [hnextRight, D5.S0.Tower.Tribonacci.Substitution.levelEmbedding_value]
          change D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i) - x =
              (t⁻¹ - (t * u - 1)) * t ^ (-((Q + 1 : Nat) : Int))
          rw [hright, D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_scale_succ Q,
            tribonacci_inverse_eq_quadratic]
          ring
  | large =>
      rcases hunit with ⟨hu0, hu1⟩
      rcases hgap with ⟨i, hleft, hright⟩
      change u <= 1 at hu1
      change x - D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
          (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i) =
        u * t ^ (-(Q : Int)) at hleft
      change D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
          (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i) - x =
        (1 - u) * t ^ (-(Q : Int)) at hright
      have hlarge :
          D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i) -
              D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i) =
            t ^ (-(Q : Int)) := by
        calc
          _ = (D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i) - x) +
              (x - D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)) := by ring
          _ = ((1 - u) + u) * t ^ (-(Q : Int)) := by rw [hleft, hright]; ring
          _ = t ^ (-(Q : Int)) := by ring
      obtain ⟨j, hset, hjleft, hjright⟩ :=
        (D5.S0.Tower.Tribonacci.Substitution.tribonacci_gap_substitution Q i).2.1 hlarge
      have hpositions :=
        D5.S0.Tower.Tribonacci.ChampionOrbit.inserted_singleton_positions Q i j hset
      by_cases hbranch : u <= t⁻¹
      · let next : Fin
            (D5.S0.Tower.Tribonacci.Names.tribonacci ((Q + 1) + 2) - 1) :=
          ⟨(D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
              (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)).1, by
            change (D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
                (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)).1 <
              D5.S0.Tower.Tribonacci.Names.tribonacci (Q + 3) - 1
            have hjBound := j.2
            omega⟩
        have hnextLeft :
            D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft (Q + 1) next =
              D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
                (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i) := by
          apply Fin.ext
          rfl
        have hnextRight :
            D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight (Q + 1) next = j := by
          apply Fin.ext
          exact hpositions.1
        simp only [
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
          if_pos hbranch]
        refine ⟨by simpa [
            D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
            hbranch] using
              tribonacci_transition_unit (⟨.large, u⟩ : State) ⟨hu0, hu1⟩,
          next, ?_, ?_⟩
        · rw [hnextLeft, D5.S0.Tower.Tribonacci.Substitution.levelEmbedding_value]
          calc
            x - D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                  (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i) =
                u * t ^ (-(Q : Int)) := hleft
            _ = (t * u) * t ^ (-((Q + 1 : Nat) : Int)) := by
              rw [D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_scale_succ Q]
              ring
        · rw [hnextRight]
          calc
            D5.S0.Tower.Tribonacci.Values.indexedNameValue (Q + 1) j - x =
                (D5.S0.Tower.Tribonacci.Values.indexedNameValue (Q + 1) j -
                    D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                      (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)) -
                  (x - D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                    (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)) := by ring
            _ = t ^ (-((Q + 1 : Nat) : Int)) - u * t ^ (-(Q : Int)) := by
              rw [hjleft, hleft]
            _ = (1 - t * u) * t ^ (-((Q + 1 : Nat) : Int)) := by
              rw [D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_scale_succ Q]
              ring
      · let next : Fin
            (D5.S0.Tower.Tribonacci.Names.tribonacci ((Q + 1) + 2) - 1) :=
          ⟨j.1, by
            change j.1 < D5.S0.Tower.Tribonacci.Names.tribonacci (Q + 3) - 1
            have hrightBound := (D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
              (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i)).2
            omega⟩
        have hnextLeft :
            D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft (Q + 1) next = j := by
          apply Fin.ext
          rfl
        have hnextRight :
            D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight (Q + 1) next =
              D5.S0.Tower.Tribonacci.Substitution.levelEmbedding Q
                (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i) := by
          apply Fin.ext
          exact hpositions.2
        simp only [
          D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
          if_neg hbranch]
        refine ⟨by simpa [
            D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator.tribonacciPeriodicTransition,
            hbranch] using
              tribonacci_transition_unit (⟨.large, u⟩ : State) ⟨hu0, hu1⟩,
          next, ?_, ?_⟩
        · rw [hnextLeft]
          calc
            x - D5.S0.Tower.Tribonacci.Values.indexedNameValue (Q + 1) j =
                (x - D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                    (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)) -
                  (D5.S0.Tower.Tribonacci.Values.indexedNameValue (Q + 1) j -
                    D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                      (D5.S0.Tower.Tribonacci.Substitution.gapLeft Q i)) := by ring
            _ = u * t ^ (-(Q : Int)) - t ^ (-((Q + 1 : Nat) : Int)) := by
              rw [hleft, hjleft]
            _ = (t * u - 1) * t ^ (-((Q + 1 : Nat) : Int)) := by
              rw [D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_scale_succ Q]
              ring
        · rw [hnextRight, D5.S0.Tower.Tribonacci.Substitution.levelEmbedding_value]
          change D5.S0.Tower.Tribonacci.Values.indexedNameValue Q
                (D5.S0.Tower.Tribonacci.Substitution.gapRight Q i) - x =
              (t - 1 - (t * u - 1)) * t ^ (-((Q + 1 : Nat) : Int))
          rw [hright, D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_scale_succ Q]
          ring

theorem tribonacci_grid_coding_iterate (Q : Nat) (x : Real) (state : State)
    (hcode : TribonacciGridCoding Q x state) (n : Nat) :
    TribonacciGridCoding (Q + n) x ((transition^[n]) state) := by
  induction n with
  | zero => simpa using hcode
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simpa [Nat.add_assoc] using tribonacci_grid_coding_transition (Q + n) x _ ih

theorem tribonacci_survivor_eq_orbit_arm (Q : Nat) (x : Real) (state : State)
    (hcode : TribonacciGridCoding Q x state) (n : Nat) :
    D5.S0.Tower.Tribonacci.Survivor.tribonacciSurvivor (Q + n) x =
      stateArm ((transition^[n]) state) := by
  exact tribonacci_survivor_eq_state_arm (Q + n) x _
    (tribonacci_grid_coding_iterate Q x state hcode n)

theorem tribonacci_ergodic_bridge_of_coding (Q : Nat) (x : Real) (state : State)
    (hcode : TribonacciGridCoding Q x state) :
    Filter.liminf
        (fun level => D5.S0.Tower.Tribonacci.Survivor.tribonacciSurvivor level x)
        Filter.atTop =
      tribonacciOrbitLowerValue state := by
  rw [← Filter.liminf_nat_add
    (fun level => D5.S0.Tower.Tribonacci.Survivor.tribonacciSurvivor level x) Q]
  unfold tribonacciOrbitLowerValue
  apply Filter.liminf_congr
  filter_upwards [] with n
  simpa [Nat.add_comm] using tribonacci_survivor_eq_orbit_arm Q x state hcode n

/-- Every internal grid point has the same lower value as a three-gap orbit. -/
theorem tribonacci_ergodic_bridge (Q : Nat) (x : Real)
    (hx : x ∈ D5.S0.Tower.Tribonacci.Survivor.tribonacciNameHull Q) :
    ∃ state : State, TribonacciUnitState state /\
      Filter.liminf
          (fun level => D5.S0.Tower.Tribonacci.Survivor.tribonacciSurvivor level x)
          Filter.atTop = tribonacciOrbitLowerValue state := by
  obtain ⟨state, hcode⟩ := tribonacci_grid_coding_exists_of_mem_hull Q x hx
  exact ⟨state, hcode.1, tribonacci_ergodic_bridge_of_coding Q x state hcode⟩

/-- All three typed state intervals occur already in the level-three grid. -/
theorem tribonacci_unit_state_has_grid_realization (state : State)
    (hunit : TribonacciUnitState state) :
    ∃ x ∈ D5.S0.Tower.Tribonacci.Survivor.tribonacciNameHull 3,
      TribonacciGridCoding 3 x state := by
  rcases D5.S0.Tower.Tribonacci.Gaps.three_gaps_occur 3 (by omega) with
    ⟨⟨ilarge, hlarge⟩, ⟨⟨ismall, hsmall⟩, ⟨icombined, hcombined⟩⟩⟩
  rcases state with ⟨kind, u⟩
  rcases hunit with ⟨hu0, hu1⟩
  cases kind with
  | large =>
      change u <= 1 at hu1
      apply tribonacci_large_state_realized_in_gap 3 ilarge u hu0 hu1
      simpa [D5.S0.Tower.Tribonacci.Gaps.indexedGap,
        D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft,
        D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight] using hlarge
  | small =>
      change u <= t⁻¹ at hu1
      apply tribonacci_small_state_realized_in_gap 3 ismall u hu0 hu1
      simpa [D5.S0.Tower.Tribonacci.Gaps.indexedGap, zpow_neg,
        D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft,
        D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight] using hsmall
  | combined =>
      change u <= t - 1 at hu1
      apply tribonacci_combined_state_realized_in_gap 3 icombined u hu0 hu1
      simpa [D5.S0.Tower.Tribonacci.Gaps.indexedGap,
        D5.S0.Tower.Tribonacci.Survivor.tribonacciGapLeft,
        D5.S0.Tower.Tribonacci.Survivor.tribonacciGapRight] using hcombined

/-- Conversely, every typed unit state has an internal grid realization. -/
theorem tribonacci_ergodic_bridge_reverse (state : State)
    (hunit : TribonacciUnitState state) :
    ∃ x ∈ D5.S0.Tower.Tribonacci.Survivor.tribonacciNameHull 3,
      Filter.liminf
          (fun level => D5.S0.Tower.Tribonacci.Survivor.tribonacciSurvivor level x)
          Filter.atTop = tribonacciOrbitLowerValue state := by
  obtain ⟨x, hx, hcode⟩ := tribonacci_unit_state_has_grid_realization state hunit
  exact ⟨x, hx, tribonacci_ergodic_bridge_of_coding 3 x state hcode⟩

def tribonacciGridLowerValues : Set Real :=
  {value | ∃ Q : Nat,
    ∃ x ∈ D5.S0.Tower.Tribonacci.Survivor.tribonacciNameHull Q,
      value = Filter.liminf
        (fun level => D5.S0.Tower.Tribonacci.Survivor.tribonacciSurvivor level x)
        Filter.atTop}

def tribonacciErgodicLowerValues : Set Real :=
  {value | ∃ state : State,
    TribonacciUnitState state /\ value = tribonacciOrbitLowerValue state}

theorem tribonacci_lower_value_sets_eq :
    tribonacciGridLowerValues = tribonacciErgodicLowerValues := by
  ext value
  constructor
  · rintro ⟨Q, x, hx, hvalue⟩
    obtain ⟨state, hunit, hbridge⟩ := tribonacci_ergodic_bridge Q x hx
    exact ⟨state, hunit, hvalue.trans hbridge⟩
  · rintro ⟨state, hunit, hvalue⟩
    obtain ⟨x, hx, hbridge⟩ := tribonacci_ergodic_bridge_reverse state hunit
    exact ⟨3, x, hx, hvalue.trans hbridge.symm⟩

noncomputable def tribonacciGridOptimalValue : Real := sSup tribonacciGridLowerValues

noncomputable def tribonacciErgodicOptimalValue : Real :=
  sSup tribonacciErgodicLowerValues

/-- The internal Tribonacci champion objective is the three-gap ergodic optimum. -/
theorem tribonacci_optimal_value_eq_ergodic_optimal_value :
    tribonacciGridOptimalValue = tribonacciErgodicOptimalValue := by
  rw [tribonacciGridOptimalValue, tribonacciErgodicOptimalValue,
    tribonacci_lower_value_sets_eq]

end D5.S0.Tower.ErgodicBridge.Tribonacci
