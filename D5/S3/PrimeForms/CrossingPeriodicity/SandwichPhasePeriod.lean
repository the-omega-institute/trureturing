/- GID: D5/S3/PrimeForms/CrossingPeriodicity/SandwichPhasePeriod
   generality: I
   mirror-B: D5/B/S3/PrimeForms/CrossingPeriodicity/SandwichPhasePeriod
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The sandwich winding phase falls by two each step and first returns mod twelve at six. -/

import D5.S3.PrimeForms.Crossing.WindingOrbitZero

/- Library-search audit trail (2026-08-19):
   * Searched for the object, not the name: the displacement law for `crossingSandwich`
     already exists inside `WindingOrbitZero`, but every step of it is `private`, and that
     module carries a frozen ledger entry, so its declaration set may not be widened.
     The public route is used instead: `ExactPropagation.rademacherPhi_mul_crossing`,
     `rademacherPhi_crossing_mul`, and `rademacherPhi_crossingMatrix` compose to the same
     single-step law without touching the frozen surface.
   * The statement proved here is not in that module: it is the *periodicity* half of the
     source law, namely that the phase first returns modulo twelve after exactly six steps.
     `WindingOrbitZero` proves only that the orbit meets phase zero once.
   * Pinned-Mathlib searches for a modular-period theorem on constant-step iterates found
     no theorem matching this statement; `Function.iterate_succ_apply'` supplies the
     induction step and is applied rather than reproved.
   * Placement: `D5/S3/PrimeForms/Crossing` already held twelve files, the SL-003 admission
     limit, so a thirteenth would be refused. A nested `Crossing/Periodicity/` bucket was
     tried first and rejected by the GID grammar, which admits three or four segments after
     `D5` and not five. The bucket is therefore a sibling of `Crossing`, and since SL-003
     counts files rather than entries, adding it leaves `PrimeForms` at its twelve.
-/

namespace D5.S3.PrimeForms.CrossingPeriodicity.SandwichPhasePeriod

open D5.S3.PrimeForms.Crossing.ExactPropagation
open D5.S3.PrimeForms.Crossing.WindingOrbitZero

/-- The public spelling of the hypotheses carried by the crossing-sandwich orbit. -/
structure Admissible (A : PositiveMatrix) : Prop where
  a_pos : 0 < A.a
  c_pos : 0 < A.c
  d_pos : 0 < A.d
  det : A.a * A.d = A.b * A.c + 1

theorem admissible_mul_crossing {A : PositiveMatrix} (hA : Admissible A) :
    Admissible (A.mul crossingMatrix) := by
  obtain ⟨ha, hc, hd, hdet⟩ := hA
  have hdetZ : (A.a : Int) * A.d = (A.b : Int) * A.c + 1 := by exact_mod_cast hdet
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [PositiveMatrix.mul, crossingMatrix]; omega
  · simp only [PositiveMatrix.mul, crossingMatrix]; omega
  · simp only [PositiveMatrix.mul, crossingMatrix]; omega
  · simp only [PositiveMatrix.mul, crossingMatrix]
    zify
    linear_combination hdetZ

theorem admissible_crossing_mul {A : PositiveMatrix} (hA : Admissible A) :
    Admissible (crossingMatrix.mul A) := by
  obtain ⟨ha, hc, hd, hdet⟩ := hA
  have hdetZ : (A.a : Int) * A.d = (A.b : Int) * A.c + 1 := by exact_mod_cast hdet
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [PositiveMatrix.mul, crossingMatrix]; omega
  · simp only [PositiveMatrix.mul, crossingMatrix]; omega
  · simp only [PositiveMatrix.mul, crossingMatrix]; omega
  · simp only [PositiveMatrix.mul, crossingMatrix]
    zify
    linear_combination hdetZ

theorem admissible_sandwich {A : PositiveMatrix} (hA : Admissible A) :
    Admissible (crossingSandwich A) :=
  admissible_crossing_mul (admissible_mul_crossing hA)

/-- Admissibility survives every number of sandwich steps. -/
theorem admissible_iterate {A : PositiveMatrix} (hA : Admissible A) (n : Nat) :
    Admissible ((crossingSandwich^[n]) A) := by
  induction n with
  | zero => simpa using hA
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact admissible_sandwich ih

/-- One sandwich step lowers the winding phase by exactly two. -/
theorem phase_sandwich_step {A : PositiveMatrix} (hA : Admissible A) :
    windingPhase (crossingSandwich A) = windingPhase A - 2 := by
  obtain ⟨ha, hc, hd, hdet⟩ := hA
  have hAM := admissible_mul_crossing (A := A) ⟨ha, hc, hd, hdet⟩
  have hright : rademacherPhi (A.mul crossingMatrix) =
      rademacherPhi A + rademacherPhi crossingMatrix - 3 :=
    rademacherPhi_mul_crossing A hc hd hdet
  have hleft : rademacherPhi (crossingMatrix.mul (A.mul crossingMatrix)) =
      rademacherPhi crossingMatrix + rademacherPhi (A.mul crossingMatrix) - 3 :=
    rademacherPhi_crossing_mul (A.mul crossingMatrix) hAM.a_pos hAM.c_pos hAM.d_pos hAM.det
  simp only [crossingSandwich, windingPhase, hleft, hright, rademacherPhi_crossingMatrix]
  ring

/-- After `n` steps the phase has fallen by exactly `2n`. -/
theorem phase_sandwich_iterate {A : PositiveMatrix} (hA : Admissible A) (n : Nat) :
    windingPhase ((crossingSandwich^[n]) A) = windingPhase A - 2 * n := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hk : Admissible ((crossingSandwich^[k]) A) := admissible_iterate hA k
      rw [Function.iterate_succ_apply', phase_sandwich_step hk, ih]
      push_cast
      ring

/-- Six steps lower the phase by exactly twelve, so the phase returns modulo twelve. -/
theorem phase_returns_after_six {A : PositiveMatrix} (hA : Admissible A) (n : Nat) :
    windingPhase ((crossingSandwich^[n + 6]) A) =
      windingPhase ((crossingSandwich^[n]) A) - 12 := by
  rw [phase_sandwich_iterate hA, phase_sandwich_iterate hA]
  push_cast
  ring

/-- No positive step count below six returns the phase modulo twelve. -/
theorem no_return_before_six {A : PositiveMatrix} (hA : Admissible A) (p : Nat)
    (hp : 0 < p) (hlt : p < 6) :
    ¬ ∃ j : Int, windingPhase ((crossingSandwich^[p]) A) - windingPhase A = 12 * j := by
  rintro ⟨j, hj⟩
  rw [phase_sandwich_iterate hA] at hj
  have h2p : (-(2 * (p : Rat))) = 12 * (j : Rat) := by linarith
  have hpj : (p : Rat) = -6 * (j : Rat) := by linarith
  have hcast : (p : Int) = -6 * j := by exact_mod_cast hpj
  omega

/-- The periodicity law: the phase falls by two each step, first returns modulo twelve at
six steps, and at no smaller positive step count. -/
theorem sandwich_phase_period_package {A : PositiveMatrix} (hA : Admissible A) :
    windingPhase (crossingSandwich A) = windingPhase A - 2 ∧
      (∀ n : Nat, windingPhase ((crossingSandwich^[n + 6]) A) =
        windingPhase ((crossingSandwich^[n]) A) - 12) ∧
      ∀ p : Nat, 0 < p → p < 6 →
        ¬ ∃ j : Int, windingPhase ((crossingSandwich^[p]) A) - windingPhase A = 12 * j :=
  ⟨phase_sandwich_step hA, phase_returns_after_six hA, no_return_before_six hA⟩

#print axioms sandwich_phase_period_package

end D5.S3.PrimeForms.CrossingPeriodicity.SandwichPhasePeriod
