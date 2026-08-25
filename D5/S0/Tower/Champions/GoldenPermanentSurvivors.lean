/- GID: D5/S0/Tower/Champions/GoldenPermanentSurvivors
   generality: I
   mirror-B: D5/B/S0/Tower/Champions/GoldenPermanentSurvivors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strict permanent survival is empty; closed survival has a larger carrier. -/

import D5.S0.Tower.Champions.GoldenSurvivorClassification

/- Library-search audit trail (2026-08-17):
   * Repository search found the exact pointwise strict-survival result
     `golden_no_strict_permanent_survivor` and the seven-state sufficient
     carrier `IsGoldenClosedPreperiodicState` in the imported frozen module.
   * The set-level statements below are the thinnest honest wrappers around
     those exact hits; no result in the repository or pinned Mathlib was used
     to identify the full closed permanent set. -/

namespace D5.S0.Tower.Champions.GoldenPermanentSurvivors

/-- States that survive every finite backward depth for the strict threshold. -/
def goldenStrictPermanentSet :
    Set D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState :=
  {state | ∀ n, state ∈
    D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenBackwardSurvivor
      D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenStrictSurvivorSet n}

/-- States that survive every finite backward depth for the closed threshold. -/
def goldenClosedPermanentSet :
    Set D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState :=
  {state | ∀ n, state ∈
    D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenBackwardSurvivor
      D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenClosedSurvivorSet n}

/-- The lower endpoint of the large-gap closed threshold interval. -/
noncomputable def goldenThresholdPoint :
    D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState :=
  ⟨.large, D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenThreshold⟩

/-- The threshold point together with the frozen seven-state preperiodic carrier. -/
def IsGoldenKnownClosedPreperiodicState
    (state : D5.S0.Tower.Champions.GoldenSurvivorTubes.GoldenSurvivorState) : Prop :=
  state = goldenThresholdPoint ∨
    D5.S0.Tower.Champions.GoldenSurvivorClassification.IsGoldenClosedPreperiodicState
      state

/-- The strict threshold has no permanently surviving state. -/
theorem golden_strict_permanent_set_eq_empty : goldenStrictPermanentSet = ∅ := by
  ext state
  simp only [goldenStrictPermanentSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  have hno :=
    D5.S0.Tower.Champions.GoldenSurvivorClassification.golden_no_strict_permanent_survivor
  exact hno state

/-- The large-gap threshold point belongs to the closed threshold domain. -/
theorem golden_threshold_point_mem_closed :
    goldenThresholdPoint ∈
      D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenClosedSurvivorSet := by
  rw [goldenThresholdPoint,
    D5.S0.Tower.Champions.GoldenSurvivorTubes.golden_closed_large_iff]
  constructor
  · exact le_rfl
  · rw [D5.S0.Tower.Champions.GoldenSurvivorTubes.golden_threshold_eq]
    have hpos := D5.S0.Tower.Champions.GoldenSurvivorTubes.golden_inverse_pos
    have hlt := D5.S0.Tower.Champions.GoldenSurvivorTubes.golden_inverse_lt_one
    nlinarith [Real.one_lt_goldenRatio]

/-- The large-gap threshold point maps directly to the four-point tail. -/
theorem golden_threshold_point_transition :
    D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenTransition goldenThresholdPoint =
      D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenTailPoint := by
  have hbranch :
      D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenThreshold ≤
        D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse := by
    rw [D5.S0.Tower.Champions.GoldenSurvivorTubes.golden_threshold_eq]
    have hpos := D5.S0.Tower.Champions.GoldenSurvivorTubes.golden_inverse_pos
    have hlt := D5.S0.Tower.Champions.GoldenSurvivorTubes.golden_inverse_lt_one
    nlinarith
  simp only [D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenTransition,
    goldenThresholdPoint, hbranch, ↓reduceIte,
    D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenTailPoint]
  congr 1
  rw [D5.S0.Tower.Champions.GoldenSurvivorTubes.golden_threshold_eq]
  calc
    Real.goldenRatio *
        (D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse ^ 2 / 2) =
        (D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse *
          Real.goldenRatio) *
          D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse / 2 := by
      ring
    _ = D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenInverse / 2 := by
      rw [D5.S0.Tower.Champions.GoldenSurvivorTubes.golden_inverse_mul, one_mul]

/-- The large-gap threshold point survives every closed backward depth. -/
theorem golden_threshold_point_permanent :
    goldenThresholdPoint ∈ goldenClosedPermanentSet := by
  intro depth
  cases depth with
  | zero => exact golden_threshold_point_mem_closed
  | succ n =>
      rw [D5.S0.Tower.Champions.GoldenSurvivorTubes.golden_backward_survivor_succ]
      constructor
      · exact golden_threshold_point_mem_closed
      · change
          D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenTransition
              goldenThresholdPoint ∈
            D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenBackwardSurvivor
              D5.S0.Tower.Champions.GoldenSurvivorTubes.goldenClosedSurvivorSet n
        rw [golden_threshold_point_transition]
        have hsurvives :=
          D5.S0.Tower.Champions.GoldenSurvivorClassification.golden_closed_preperiodic_survives
        apply hsurvives n
        exact Or.inr (Or.inr (Or.inr (Or.inl (Eq.refl _))))

/-- Every state in the known eight-state preperiodic carrier survives the
closed threshold permanently.  This is a proved lower bound, not an equality. -/
theorem golden_known_closed_preperiodic_carrier_subset :
    {state | IsGoldenKnownClosedPreperiodicState state} ⊆ goldenClosedPermanentSet := by
  intro state hstate n
  rcases hstate with hthreshold | hpreperiodic
  · subst state
    exact golden_threshold_point_permanent n
  · have hsurvives :=
      D5.S0.Tower.Champions.GoldenSurvivorClassification.golden_closed_preperiodic_survives
    exact hsurvives n state hpreperiodic

end D5.S0.Tower.Champions.GoldenPermanentSurvivors
