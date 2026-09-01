/- GID: D5/S0/Tower/EndpointCycle/GapEndpoints
   generality: I
   mirror-B: D5/B/S0/Tower/EndpointCycle/GapEndpoints
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The three gap right endpoints form a period-three transition cycle. -/

import D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration

/- Library-search audit trail (2026-08-18):
   * Repository search found the transition, the gap lengths, and the inverse
     polynomial identity, but no statement about the orbit through the gap
     endpoints.
   * The cycle was found while reconciling two enumeration counts that
     disagreed: the combinatorial closed-itinerary count and a real-coordinate
     filter differed by exactly three at period nine, and the three words were
     the rotations of this cycle.  Its coordinates sit exactly on the gap
     boundaries, which is why a floating comparison there is not decidable by
     precision. -/

namespace D5.S0.Tower.EndpointCycle.GapEndpoints

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant

/-- The right endpoint of the large gap, as a state. -/
noncomputable def largeEndpoint : TribonacciPeriodicState := ⟨.large, 1⟩

/-- The right endpoint of the combined gap. -/
noncomputable def combinedEndpoint : TribonacciPeriodicState := ⟨.combined, t - 1⟩

/-- The right endpoint of the small gap. -/
noncomputable def smallEndpoint : TribonacciPeriodicState := ⟨.small, t⁻¹⟩

theorem one_lt_t : (1 : Real) < t :=
  D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant

theorem t_lt_two : t < 2 :=
  D5.S0.Tower.Tribonacci.Values.tribonacciConstant_lt_two

theorem t_pos : (0 : Real) < t := lt_trans zero_lt_one one_lt_t

theorem inv_t_lt_one : t⁻¹ < 1 := by
  rw [inv_lt_one_iff₀]; right; exact one_lt_t

/-- Each coordinate is exactly its own gap's length. -/
theorem endpoints_are_gap_lengths :
    largeEndpoint.coordinate = tribonacciPeriodicGapLength largeEndpoint.kind ∧
      combinedEndpoint.coordinate =
        tribonacciPeriodicGapLength combinedEndpoint.kind ∧
      smallEndpoint.coordinate = tribonacciPeriodicGapLength smallEndpoint.kind := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [largeEndpoint, combinedEndpoint, smallEndpoint,
      tribonacciPeriodicGapLength]

/-- The large endpoint maps to the combined endpoint. -/
theorem large_to_combined :
    tribonacciPeriodicTransition largeEndpoint = combinedEndpoint := by
  have hbranch : ¬ (largeEndpoint.coordinate ≤ t⁻¹) := by
    change ¬ ((1 : Real) ≤ t⁻¹)
    push_neg
    exact inv_t_lt_one
  rw [tribonacciPeriodicTransition.eq_1,
    show largeEndpoint.kind = .large by rfl]
  simp only [if_neg hbranch]
  simp only [largeEndpoint, combinedEndpoint]
  norm_num

/-- The combined endpoint maps to the small endpoint.  This step is where the
Tribonacci relation enters: the image coordinate is `t^2 - t - 1`, which is the
inverse of the constant, and that is the small gap's length. -/
theorem combined_to_small :
    tribonacciPeriodicTransition combinedEndpoint = smallEndpoint := by
  have hinv := tribonacci_inverse_polynomial
  have hbranch : ¬ (combinedEndpoint.coordinate ≤ t⁻¹) := by
    change ¬ (t - 1 ≤ t⁻¹)
    push_neg
    rw [hinv]
    nlinarith [one_lt_t, t_lt_two,
      D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic]
  rw [tribonacciPeriodicTransition.eq_1,
    show combinedEndpoint.kind = .combined by rfl]
  simp only [if_neg hbranch]
  simp only [combinedEndpoint, smallEndpoint,
    TribonacciPeriodicState.mk.injEq, true_and]
  rw [hinv]
  ring

/-- The small endpoint maps back to the large endpoint, closing the cycle. -/
theorem small_to_large :
    tribonacciPeriodicTransition smallEndpoint = largeEndpoint := by
  have hne : t ≠ 0 := ne_of_gt t_pos
  simp only [smallEndpoint, largeEndpoint, tribonacciPeriodicTransition,
    TribonacciPeriodicState.mk.injEq, true_and]
  field_simp

/-- The three gap right endpoints form a cycle of period three, and each
coordinate is exactly the length of the gap it sits in.  A state on this cycle
is on the boundary of its gap, so whether it belongs is a matter of whether gaps
are taken closed or half open, not a matter of computing more precisely. -/
theorem gap_endpoints_form_a_three_cycle :
    tribonacciPeriodicTransition largeEndpoint = combinedEndpoint ∧
      tribonacciPeriodicTransition combinedEndpoint = smallEndpoint ∧
        tribonacciPeriodicTransition smallEndpoint = largeEndpoint ∧
          largeEndpoint.coordinate =
            tribonacciPeriodicGapLength largeEndpoint.kind ∧
            combinedEndpoint.coordinate =
              tribonacciPeriodicGapLength combinedEndpoint.kind ∧
              smallEndpoint.coordinate =
                tribonacciPeriodicGapLength smallEndpoint.kind :=
  ⟨large_to_combined, combined_to_small, small_to_large,
    endpoints_are_gap_lengths.1, endpoints_are_gap_lengths.2.1,
    endpoints_are_gap_lengths.2.2⟩

end D5.S0.Tower.EndpointCycle.GapEndpoints
