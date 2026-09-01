/- GID: D5/S0/Tower/Champions/GoldenSurvivorClassification
   generality: I
   mirror-B: D5/B/S0/Tower/Champions/GoldenSurvivorClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Four backward-survivor tubes converge exactly to the golden champion states. -/

import D5.S0.Tower.Champions.GoldenSurvivorTubes

/- Library-search audit trail (2026-08-16):
   * Repository search found no backward-limit classification beyond the exact
     finite-depth tube theorem in the imported sibling module.
   * Pinned mathlib's `exists_pow_lt_of_lt_one` supplies the standard geometric
     limit step.  No external or third-party theorem identifies these four
     golden states, so the componentwise argument is local. -/

namespace D5.S0.Tower.Champions.GoldenSurvivorClassification

open D5.S0.Tower.Champions.GoldenSurvivorTubes
open D5.S0.Conventions
open D5.S0.Tower.GoldenGaps
open D5.S0.Tower.GoldenNames
open D5.S0.Tower.MetricGeometry.GoldenSurvivor

local notation "φ" => Real.goldenRatio

/-- A state belongs to every componentwise closed finite-depth tube. -/
def goldenBackwardLimitCore : Set GoldenSurvivorState :=
  {state | ∀ n, goldenClosedTube n state}

/-- The four nondegenerate components of strict backward survival converge to
exactly the source's three-state ring and its one-step preimage. -/
theorem golden_backward_limit_core_eq_four_points :
    goldenBackwardLimitCore = goldenFourPointSet := by
  ext state
  change (∀ n, goldenClosedTube n state) ↔ state ∈ goldenFourPointSet
  constructor
  · intro hcore
    rcases state with ⟨kind, u⟩
    cases kind with
    | large =>
        by_cases htail : u ≤ goldenInverse / 2
        · have hlow (n : Nat) : (goldenTubeLows n).tail ≤ u := by
            rcases hcore n with hA | hB | hC
            · exact hA.1
            · nlinarith [(golden_tube_lows_bounds n).2.2.1]
            · nlinarith [(golden_tube_lows_bounds n).2.2.2.2.1,
                golden_half_le_inverse]
          have hu : u = goldenInverse / 2 := by
            apply le_antisymm htail
            by_contra hne
            have hlt : u < goldenInverse / 2 := lt_of_not_ge hne
            obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
              (sub_pos.mpr hlt) golden_inverse_lt_one
            have hradius := (golden_tube_radii n).1
            nlinarith [hlow n]
          simp only [goldenFourPointSet, Set.mem_insert_iff, Set.mem_singleton_iff]
          exact Or.inl (by simp [goldenTailPoint, hu])
        · have htail' : goldenInverse / 2 < u := lt_of_not_ge htail
          by_cases hmid : u ≤ 1 / 2
          · have hlow (n : Nat) : (goldenTubeLows n).midpoint ≤ u := by
              rcases hcore n with hA | hB | hC
              · nlinarith [hA.2]
              · exact hB.1
              · nlinarith [(golden_tube_lows_bounds n).2.2.2.2.1,
                  golden_half_le_inverse]
            have hu : u = 1 / 2 := by
              apply le_antisymm hmid
              by_contra hne
              have hlt : u < 1 / 2 := lt_of_not_ge hne
              obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
                (sub_pos.mpr hlt) golden_inverse_lt_one
              have hradius := (golden_tube_radii n).2.1
              nlinarith [hlow n]
            simp only [goldenFourPointSet, Set.mem_insert_iff, Set.mem_singleton_iff]
            exact Or.inr (Or.inl (by simp [goldenLargeMidpoint, hu]))
          · have hmid' : (1 : Real) / 2 < u := lt_of_not_ge hmid
            have hlow (n : Nat) : (goldenTubeLows n).phiPoint ≤ u := by
              rcases hcore n with hA | hB | hC
              · nlinarith [hA.2]
              · nlinarith [hB.2]
              · exact hC.1
            have hupp : u ≤ φ / 2 := by
              rcases hcore 0 with hA | hB | hC
              · nlinarith [hA.2]
              · nlinarith [hB.2]
              · exact hC.2
            have hu : u = φ / 2 := by
              apply le_antisymm hupp
              by_contra hne
              have hlt : u < φ / 2 := lt_of_not_ge hne
              obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
                (sub_pos.mpr hlt) golden_inverse_lt_one
              have hradius := (golden_tube_radii n).2.2.1
              nlinarith [hlow n]
            simp only [goldenFourPointSet, Set.mem_insert_iff, Set.mem_singleton_iff]
            exact Or.inr (Or.inr (Or.inl (by simp [goldenLargePhiPoint, hu])))
    | small =>
        have hlow (n : Nat) : (goldenTubeLows n).small ≤ u := (hcore n).1
        have hupp : u ≤ (1 : Real) / 2 := (hcore 0).2
        have hu : u = 1 / 2 := by
          apply le_antisymm hupp
          by_contra hne
          have hlt : u < 1 / 2 := lt_of_not_ge hne
          obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
            (mul_pos golden_inverse_pos (sub_pos.mpr hlt)) golden_inverse_lt_one
          have hradius := (golden_tube_radii n).2.2.2
          have hscaled := mul_le_mul_of_nonneg_left (hlow n) golden_inverse_pos.le
          nlinarith
        simp only [goldenFourPointSet, Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inr (Or.inr (Or.inr (by simp [goldenSmallMidpoint, hu])))
  · intro hfour n
    simp only [goldenFourPointSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hfour
    rcases hfour with rfl | rfl | rfl | rfl
    · simp only [goldenClosedTube, goldenTailPoint]
      exact Or.inl ⟨(golden_tube_lows_bounds n).2.1.le, le_rfl⟩
    · simp only [goldenClosedTube, goldenLargeMidpoint]
      exact Or.inr (Or.inl ⟨(golden_tube_lows_bounds n).2.2.2.1.le, le_rfl⟩)
    · simp only [goldenClosedTube, goldenLargePhiPoint]
      exact Or.inr (Or.inr ⟨(golden_tube_lows_bounds n).2.2.2.2.2.1.le, le_rfl⟩)
    · simp only [goldenClosedTube, goldenSmallMidpoint]
      exact ⟨(golden_tube_lows_bounds n).2.2.2.2.2.2.2.le, le_rfl⟩

theorem golden_open_tube_subset_closed
    (n : Nat) (state : GoldenSurvivorState) :
    goldenOpenTube n state → goldenClosedTube n state := by
  rcases state with ⟨kind, u⟩
  cases kind with
  | large =>
      rintro (hA | hB | hC)
      · exact Or.inl ⟨hA.1.le, hA.2.le⟩
      · exact Or.inr (Or.inl ⟨hB.1.le, hB.2.le⟩)
      · exact Or.inr (Or.inr ⟨hC.1.le, hC.2.le⟩)
  | small =>
      rintro h
      exact ⟨h.1.le, h.2.le⟩

/-- No state remains forever in the strict-above-threshold set.  The proof
uses the four-point limit classification and then checks that every limiting
point is an excluded endpoint of the depth-two open tubes. -/
theorem golden_no_strict_permanent_survivor (state : GoldenSurvivorState) :
    ¬∀ n, state ∈ goldenBackwardSurvivor goldenStrictSurvivorSet n := by
  intro hpermanent
  have hclosed : state ∈ goldenBackwardLimitCore := by
    intro n
    exact golden_open_tube_subset_closed n state
      ((golden_backward_survivor_four_tubes n state).mp (hpermanent (n + 2)))
  have hfour : state ∈ goldenFourPointSet := by
    rw [← golden_backward_limit_core_eq_four_points]
    exact hclosed
  have hopen := (golden_backward_survivor_four_tubes 0 state).mp (hpermanent 2)
  simp only [goldenFourPointSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hfour
  rcases hfour with rfl | rfl | rfl | rfl
  · simp only [goldenOpenTube, goldenTubeLows, goldenInitialTubeLows, goldenTailPoint] at hopen
    rw [golden_threshold_eq, golden_inverse_sq, golden_inverse_eq_sub_one] at hopen
    rcases hopen with hA | hB | hC <;>
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  · simp only [goldenOpenTube, goldenTubeLows, goldenInitialTubeLows,
      goldenLargeMidpoint] at hopen
    rw [golden_inverse_eq_sub_one] at hopen
    rcases hopen with hA | hB | hC <;>
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  · simp only [goldenOpenTube, goldenTubeLows, goldenInitialTubeLows,
      goldenLargePhiPoint] at hopen
    rw [golden_inverse_eq_sub_one] at hopen
    rcases hopen with hA | hB | hC <;>
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  · simp only [goldenOpenTube, goldenTubeLows, goldenInitialTubeLows,
      goldenSmallMidpoint] at hopen
    rw [golden_inverse_eq_sub_one] at hopen
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]

/-- A higher preperiodic large-gap state omitted by the source's claimed
classification of the closed permanent survivor set. -/
noncomputable def goldenHigherPreimage : GoldenSurvivorState :=
  ⟨.large, goldenInitialTubeLows.midpoint⟩

noncomputable def goldenRightPreimage : GoldenSurvivorState :=
  ⟨.large, goldenInitialTubeLows.phiPoint⟩

noncomputable def goldenSmallPreimage : GoldenSurvivorState :=
  ⟨.small, goldenInverse / 2⟩

example : goldenTransition goldenHigherPreimage = goldenRightPreimage := by
  simp only [goldenHigherPreimage, goldenRightPreimage, goldenInitialTubeLows]
  simp only [goldenTransition]
  rw [if_pos (by
    rw [golden_inverse_eq_sub_one]
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio])]
  congr 1
  change φ * ((9 - 5 * φ) / 2) = (4 * φ - 5) / 2
  nlinarith [Real.goldenRatio_sq]

example : goldenTransition goldenRightPreimage = goldenSmallPreimage := by
  simp only [goldenRightPreimage, goldenSmallPreimage, goldenInitialTubeLows]
  simp only [goldenTransition]
  rw [if_neg (by
    rw [golden_inverse_eq_sub_one]
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio])]
  congr 1
  change φ ^ 2 * ((4 * φ - 5) / 2) - φ = goldenInverse / 2
  rw [golden_inverse_eq_sub_one]
  have hphi3 : φ ^ 3 = 2 * φ + 1 := by
    calc
      φ ^ 3 = φ * φ ^ 2 := by ring
      _ = φ * (φ + 1) := by rw [Real.goldenRatio_sq]
      _ = 2 * φ + 1 := by nlinarith [Real.goldenRatio_sq]
  rw [show φ ^ 2 * ((4 * φ - 5) / 2) - φ =
      (4 * φ ^ 3 - 5 * φ ^ 2) / 2 - φ by ring]
  rw [Real.goldenRatio_sq, hphi3]
  ring

example : goldenTransition goldenSmallPreimage = goldenTailPoint := by
  norm_num only [goldenTransition, goldenSmallPreimage, goldenTailPoint]

def IsGoldenClosedPreperiodicState (state : GoldenSurvivorState) : Prop :=
  state = goldenHigherPreimage ∨ state = goldenRightPreimage ∨
    state = goldenSmallPreimage ∨ state = goldenTailPoint ∨
    state = goldenLargeMidpoint ∨ state = goldenLargePhiPoint ∨
    state = goldenSmallMidpoint

theorem golden_closed_preperiodic_mem (state : GoldenSurvivorState)
    (hstate : IsGoldenClosedPreperiodicState state) :
    state ∈ goldenClosedSurvivorSet := by
  rcases hstate with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [goldenHigherPreimage]
    rw [golden_closed_large_iff]
    simp only [goldenInitialTubeLows]
    rw [golden_threshold_eq, golden_inverse_sq]
    constructor <;> nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  · simp only [goldenRightPreimage]
    rw [golden_closed_large_iff]
    simp only [goldenInitialTubeLows]
    rw [golden_threshold_eq, golden_inverse_sq]
    constructor <;> nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  · simp only [goldenSmallPreimage]
    rw [golden_closed_small_iff]
    constructor <;> nlinarith [golden_inverse_pos, golden_inverse_lt_one]
  · simp only [goldenTailPoint]
    rw [golden_closed_large_iff]
    rw [golden_threshold_eq]
    constructor <;> nlinarith [golden_inverse_pos, golden_inverse_lt_one,
      golden_inverse_lt_phi_half]
  · simp only [goldenLargeMidpoint]
    rw [golden_closed_large_iff]
    rw [golden_threshold_eq]
    constructor <;> nlinarith [golden_inverse_pos, golden_inverse_lt_one,
      golden_half_le_inverse, golden_inverse_lt_phi_half]
  · simp only [goldenLargePhiPoint]
    rw [golden_closed_large_iff]
    rw [golden_threshold_eq]
    constructor <;> nlinarith [golden_inverse_pos, golden_inverse_lt_one,
      Real.one_lt_goldenRatio]
  · simp only [goldenSmallMidpoint]
    rw [golden_closed_small_iff]
    constructor <;> nlinarith [golden_inverse_pos, golden_inverse_lt_one]

theorem golden_closed_preperiodic_forward (state : GoldenSurvivorState)
    (hstate : IsGoldenClosedPreperiodicState state) :
    IsGoldenClosedPreperiodicState (goldenTransition state) := by
  rcases hstate with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · right
    left
    exact (by
      simp only [goldenHigherPreimage, goldenRightPreimage, goldenInitialTubeLows]
      simp only [goldenTransition]
      rw [if_pos (by
        rw [golden_inverse_eq_sub_one]
        nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio])]
      congr 1
      change φ * ((9 - 5 * φ) / 2) = (4 * φ - 5) / 2
      nlinarith [Real.goldenRatio_sq])
  · right
    right
    left
    exact (by
      simp only [goldenRightPreimage, goldenSmallPreimage, goldenInitialTubeLows]
      simp only [goldenTransition]
      rw [if_neg (by
        rw [golden_inverse_eq_sub_one]
        nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio])]
      congr 1
      change φ ^ 2 * ((4 * φ - 5) / 2) - φ = goldenInverse / 2
      rw [golden_inverse_eq_sub_one]
      have hphi3 : φ ^ 3 = 2 * φ + 1 := by
        calc
          φ ^ 3 = φ * φ ^ 2 := by ring
          _ = φ * (φ + 1) := by rw [Real.goldenRatio_sq]
          _ = 2 * φ + 1 := by nlinarith [Real.goldenRatio_sq]
      rw [show φ ^ 2 * ((4 * φ - 5) / 2) - φ =
          (4 * φ ^ 3 - 5 * φ ^ 2) / 2 - φ by ring]
      rw [Real.goldenRatio_sq, hphi3]
      ring)
  · right; right; right; left
    norm_num only [goldenTransition, goldenSmallPreimage, goldenTailPoint]
  · right; right; right; right; left
    simp only [goldenTailPoint, goldenLargeMidpoint]
    simp only [goldenTransition]
    rw [if_pos golden_inverse_half_le_inverse]
    change (⟨.large, φ * (goldenInverse / 2)⟩ : GoldenSurvivorState) =
      ⟨.large, (1 : ℝ) / 2⟩
    congr 1
    change φ * (goldenInverse / 2) = (1 : ℝ) / 2
    nlinarith [golden_inverse_mul]
  · right; right; right; right; right; left
    simp only [goldenLargeMidpoint, goldenLargePhiPoint]
    simp only [goldenTransition]
    rw [if_pos golden_half_le_inverse]
    congr 1
    change φ * ((1 : ℝ) / 2) = φ / 2
    ring
  · right; right; right; right; right; right
    simp only [goldenLargePhiPoint, goldenSmallMidpoint]
    simp only [goldenTransition]
    rw [if_neg (not_le.mpr golden_inverse_lt_phi_half)]
    congr 1
    change φ ^ 2 * (φ / 2) - φ = (1 : ℝ) / 2
    have hphi3 : φ ^ 3 = 2 * φ + 1 := by
      calc
        φ ^ 3 = φ * φ ^ 2 := by ring
        _ = φ * (φ + 1) := by rw [Real.goldenRatio_sq]
        _ = 2 * φ + 1 := by nlinarith [Real.goldenRatio_sq]
    rw [show φ ^ 2 * (φ / 2) - φ = φ ^ 3 / 2 - φ by ring]
    rw [hphi3]
    ring
  · right; right; right; right; left
    norm_num only [goldenTransition, goldenSmallMidpoint, goldenLargeMidpoint]

theorem golden_closed_preperiodic_survives
    (n : Nat) (state : GoldenSurvivorState)
    (hstate : IsGoldenClosedPreperiodicState state) :
    state ∈ goldenBackwardSurvivor goldenClosedSurvivorSet n := by
  induction n generalizing state with
  | zero => exact golden_closed_preperiodic_mem state hstate
  | succ n ih =>
      rw [golden_backward_survivor_succ]
      exact ⟨golden_closed_preperiodic_mem state hstate,
        ih (goldenTransition state) (golden_closed_preperiodic_forward state hstate)⟩

/-- The source's stronger claim about `Fbar`-permanent states is false: the
higher preimage survives every closed backward depth but is not one of four. -/
theorem golden_closed_permanent_not_four_points :
    ∃ state, (∀ n, state ∈ goldenBackwardSurvivor goldenClosedSurvivorSet n) ∧
      state ∉ goldenFourPointSet := by
  refine ⟨goldenHigherPreimage, ?_, ?_⟩
  · intro n
    exact golden_closed_preperiodic_survives n goldenHigherPreimage (Or.inl rfl)
  · simp only [goldenFourPointSet, Set.mem_insert_iff, Set.mem_singleton_iff,
      goldenHigherPreimage, goldenTailPoint, goldenLargeMidpoint,
      goldenLargePhiPoint, goldenSmallMidpoint, goldenInitialTubeLows]
    rw [golden_inverse_eq_sub_one]
    simp only [not_or]
    constructor
    · intro h
      have := congrArg GoldenSurvivorState.coordinate h
      dsimp at this
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
    constructor
    · intro h
      have := congrArg GoldenSurvivorState.coordinate h
      dsimp at this
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
    constructor
    · intro h
      have := congrArg GoldenSurvivorState.coordinate h
      dsimp at this
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
    · intro h
      have := congrArg GoldenSurvivorState.kind h
      simp at this

/-- The last grid index, needed to audit the real-line boundary point `x=1`. -/
def goldenLastIndex (Q : Nat) : Fin (Nat.fib (Q + 2)) :=
  ⟨Nat.fib (Q + 2) - 1,
    Nat.sub_lt (Nat.fib_pos.2 (by omega)) (by omega)⟩

/-- The completed terminal gap from the last grid point to one. -/
noncomputable def goldenTerminalGap (Q : Nat) : Real :=
  1 - indexedNameValue Q (goldenLastIndex Q)

theorem golden_last_wdigits_add_two (Q : Nat) :
    wdigits (Nat.fib (Q + 4) - 1) =
      (Q + 3) :: wdigits (Nat.fib (Q + 2) - 1) := by
  symm
  apply wdigits_unique
  · rw [List.IsZeckendorfRep, List.cons_append]
    have hlast : Nat.fib (Q + 2) - 1 < Nat.fib (Q + 2) :=
      Nat.sub_lt (Nat.fib_pos.2 (by omega)) (by omega)
    let i : Fin (Nat.fib (Q + 2)) := ⟨Nat.fib (Q + 2) - 1, hlast⟩
    apply (goldenNameEquiv Q i).1.2.cons
    intro k hk
    have hk_mem := List.mem_of_mem_head? hk
    rw [List.mem_append, List.mem_singleton] at hk_mem
    rcases hk_mem with hk_digits | rfl
    · have := (goldenNameEquiv Q i).2 k hk_digits
      omega
    · omega
  · simp only [List.map_cons, List.sum_cons, decode_wdigits]
    have hrec : Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) := by
      rw [Nat.fib_add_two (n := Q + 2), add_comm]
    rw [hrec]
    have hpos := Nat.fib_pos.2 (by omega : 0 < Q + 2)
    omega

theorem golden_inverse_sum : φ ^ (-1 : Int) + φ ^ (-2 : Int) = 1 := by
  have hne := Real.goldenRatio_ne_zero
  calc
    φ ^ (-1 : Int) + φ ^ (-2 : Int) =
        φ ^ (-2 : Int) * φ + φ ^ (-2 : Int) := by
      rw [show (-1 : Int) = -2 + 1 by omega, zpow_add₀ hne]
      norm_num only [zpow_ofNat, pow_one]
    _ = φ ^ (-2 : Int) * (φ + 1) := by ring
    _ = φ ^ (-2 : Int) * φ ^ 2 := by rw [Real.goldenRatio_sq]
    _ = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ hne]
      norm_num

theorem golden_indexed_last_add_two (Q : Nat) :
    indexedNameValue (Q + 2) (goldenLastIndex (Q + 2)) =
      φ ^ (-1 : Int) + φ ^ (-2 : Int) *
        indexedNameValue Q (goldenLastIndex Q) := by
  change
    ((wdigits (Nat.fib (Q + 4) - 1)).map fun k : Nat ↦
        φ ^ ((k : Int) - ((Q + 4 : Nat) : Int))).sum =
      φ ^ (-1 : Int) + φ ^ (-2 : Int) *
        ((wdigits (Nat.fib (Q + 2) - 1)).map fun k : Nat ↦
          φ ^ ((k : Int) - ((Q + 2 : Nat) : Int))).sum
  rw [golden_last_wdigits_add_two]
  simp only [List.map_cons, List.sum_cons]
  have hhead : ((Q + 3 : Nat) : Int) - ((Q + 4 : Nat) : Int) = -1 := by
    push_cast
    omega
  rw [hhead]
  congr 1
  induction wdigits (Nat.fib (Q + 2) - 1) with
  | nil => simp
  | cons k digits ih =>
      simp only [List.map_cons, List.sum_cons]
      have hexponent :
          (k : Int) - ((Q + 4 : Nat) : Int) =
            -2 + ((k : Int) - ((Q + 2 : Nat) : Int)) := by
        push_cast
        omega
      rw [hexponent, zpow_add₀ Real.goldenRatio_ne_zero, ih]
      ring

theorem golden_terminal_gap_add_two (Q : Nat) :
    goldenTerminalGap (Q + 2) = goldenTerminalGap Q * φ ^ (-2 : Int) := by
  rw [goldenTerminalGap, golden_indexed_last_add_two]
  unfold goldenTerminalGap
  calc
    1 - (φ ^ (-1 : Int) + φ ^ (-2 : Int) *
        indexedNameValue Q (goldenLastIndex Q)) =
        (1 - (φ ^ (-1 : Int) + φ ^ (-2 : Int))) +
          (1 - indexedNameValue Q (goldenLastIndex Q)) * φ ^ (-2 : Int) := by
      ring
    _ = (1 - indexedNameValue Q (goldenLastIndex Q)) * φ ^ (-2 : Int) := by
      rw [golden_inverse_sum]
      ring

theorem golden_terminal_gap_zero : goldenTerminalGap 0 = 1 := by
  have hindex : goldenLastIndex 0 = ⟨0, by norm_num [Nat.fib]⟩ := by
    apply Fin.ext
    norm_num [goldenLastIndex, Nat.fib]
  rw [goldenTerminalGap, hindex]
  change 1 - ((wdigits 0).map fun k : Nat ↦
    φ ^ ((k : Int) - (((0 : Nat) + 2 : Nat) : Int))).sum = 1
  rw [show wdigits 0 = [] by
    symm
    apply wdigits_unique
    · exact List.IsZeckendorfRep_nil
    · rfl]
  norm_num

theorem golden_terminal_gap_one : goldenTerminalGap 1 = φ ^ (-2 : Int) := by
  have hindex : goldenLastIndex 1 = ⟨1, by norm_num [Nat.fib]⟩ := by
    apply Fin.ext
    norm_num [goldenLastIndex, Nat.fib]
  rw [goldenTerminalGap, hindex]
  change 1 - ((wdigits 1).map fun k : Nat ↦
    φ ^ ((k : Int) - (((1 : Nat) + 2 : Nat) : Int))).sum = φ ^ (-2 : Int)
  rw [show wdigits 1 = [2] by
    symm
    apply wdigits_unique
    · norm_num [List.IsZeckendorfRep]
    · norm_num [Nat.fib]]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  change 1 - φ ^ (-1 : Int) = φ ^ (-2 : Int)
  linarith [golden_inverse_sum]

theorem golden_zpow_shift_two (Q : Nat) :
    φ ^ (-(Q : Int)) * φ ^ (-2 : Int) = φ ^ (-((Q + 2 : Nat) : Int)) := by
  rw [← zpow_add₀ Real.goldenRatio_ne_zero]
  congr 1
  push_cast
  omega

theorem golden_terminal_gap_even (k : Nat) :
    goldenTerminalGap (2 * k) = φ ^ (-((2 * k : Nat) : Int)) := by
  induction k with
  | zero => simpa using golden_terminal_gap_zero
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega,
        golden_terminal_gap_add_two, ih, golden_zpow_shift_two]

theorem golden_terminal_gap_odd (k : Nat) :
    goldenTerminalGap (2 * k + 1) = φ ^ (-(((2 * k + 1) + 1 : Nat) : Int)) := by
  induction k with
  | zero => simpa using golden_terminal_gap_one
  | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
        golden_terminal_gap_add_two, ih, golden_zpow_shift_two]

theorem golden_nat_even_or_odd (Q : Nat) :
    ∃ k : Nat, Q = 2 * k ∨ Q = 2 * k + 1 := by
  refine ⟨Q / 2, ?_⟩
  have hmod := Nat.mod_lt Q (by omega : 0 < 2)
  have hdecomp := Nat.mod_add_div Q 2
  omega

theorem golden_terminal_gap_pos (Q : Nat) : 0 < goldenTerminalGap Q := by
  rcases golden_nat_even_or_odd Q with ⟨k, rfl | rfl⟩
  · rw [golden_terminal_gap_even]
    positivity
  · rw [golden_terminal_gap_odd]
    positivity

theorem golden_infDist_one_eq_terminal (Q : Nat) :
    Metric.infDist 1 (goldenNameGrid Q) = goldenTerminalGap Q := by
  let last := goldenLastIndex Q
  have hlastMem : indexedNameValue Q last ∈ goldenNameGrid Q := ⟨last, rfl⟩
  have hgrid : (goldenNameGrid Q).Nonempty := ⟨indexedNameValue Q last, hlastMem⟩
  apply le_antisymm
  · calc
      Metric.infDist 1 (goldenNameGrid Q) ≤ dist 1 (indexedNameValue Q last) :=
        Metric.infDist_le_dist_of_mem hlastMem
      _ = goldenTerminalGap Q := by
        rw [Real.dist_eq, abs_of_nonneg]
        · rfl
        · change 0 ≤ 1 - indexedNameValue Q last
          exact (golden_terminal_gap_pos Q).le
  · rw [Metric.le_infDist hgrid]
    intro y hy
    rcases hy with ⟨j, rfl⟩
    have hjlast : j ≤ last := by
      change j.1 ≤ Nat.fib (Q + 2) - 1
      have hj := j.2
      omega
    have hjvalue : indexedNameValue Q j ≤ indexedNameValue Q last :=
      (indexed_nameValue_strictMono Q).monotone hjlast
    have hlastOne : indexedNameValue Q last < 1 := by
      have hgap := golden_terminal_gap_pos Q
      unfold goldenTerminalGap at hgap
      change indexedNameValue Q (goldenLastIndex Q) < 1
      linarith
    rw [Real.dist_eq, abs_of_nonneg]
    · change 1 - indexedNameValue Q last ≤ 1 - indexedNameValue Q j
      linarith
    · linarith

theorem golden_survivor_one_even (k : Nat) :
    goldenSurvivor (2 * k) 1 = 1 := by
  unfold goldenSurvivor
  rw [golden_infDist_one_eq_terminal, golden_terminal_gap_even,
    ← zpow_add₀ Real.goldenRatio_ne_zero]
  norm_num

theorem golden_survivor_one_odd (k : Nat) :
    goldenSurvivor (2 * k + 1) 1 = goldenInverse := by
  unfold goldenSurvivor
  rw [golden_infDist_one_eq_terminal, golden_terminal_gap_odd,
    ← zpow_add₀ Real.goldenRatio_ne_zero]
  congr 1
  push_cast
  omega

/-- On the frozen real-line carrier, the omitted terminal point has liminf
`phi^-1`, which is strictly above the proposed `phi^-2/2` bound. -/
theorem golden_survivor_one_liminf :
    Filter.liminf (fun Q => goldenSurvivor Q 1) Filter.atTop = goldenInverse := by
  have hlower : ∀ᶠ Q in Filter.atTop, goldenInverse ≤ goldenSurvivor Q 1 := by
    filter_upwards [] with Q
    rcases golden_nat_even_or_odd Q with ⟨k, rfl | rfl⟩
    · rw [golden_survivor_one_even]
      exact golden_inverse_lt_one.le
    · rw [golden_survivor_one_odd]
  have hupper : ∀ᶠ Q in Filter.atTop, goldenSurvivor Q 1 ≤ (1 : Real) := by
    filter_upwards [] with Q
    rcases golden_nat_even_or_odd Q with ⟨k, rfl | rfl⟩
    · rw [golden_survivor_one_even]
    · rw [golden_survivor_one_odd]
      exact golden_inverse_lt_one.le
  apply le_antisymm
  · apply Filter.liminf_le_of_frequently_le
    · rw [Filter.frequently_atTop]
      intro N
      refine ⟨2 * N + 1, by omega, ?_⟩
      rw [golden_survivor_one_odd]
    · exact ⟨goldenInverse, hlower⟩
  · exact Filter.le_liminf_of_le
      (Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop hupper) hlower

theorem golden_threshold_lt_inverse : goldenThreshold < goldenInverse := by
  rw [golden_threshold_eq]
  nlinarith [golden_inverse_pos, golden_inverse_lt_one]

/-- Consequently the requested unrestricted global upper bound is false. -/
theorem golden_global_liminf_upper_bound_false :
    ¬∀ x : Real,
      Filter.liminf (fun Q => goldenSurvivor Q x) Filter.atTop ≤ goldenThreshold := by
  intro h
  have hone := h 1
  rw [golden_survivor_one_liminf] at hone
  exact (not_le_of_gt golden_threshold_lt_inverse) hone

end D5.S0.Tower.Champions.GoldenSurvivorClassification
