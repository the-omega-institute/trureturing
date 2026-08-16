/- GID: D5/S3/PrimeForms/Crossing/WindingOrbitZero
   generality: I
   mirror-B: D5/B/S3/PrimeForms/Crossing/WindingOrbitZero
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive crossing-sandwich orbit has one winding-phase zero. -/

import D5.S3.PrimeForms.Crossing.ExactPropagation

/- Library-search audit trail (2026-08-16):
   * Repository search found `ExactPropagation.rademacherPhi_mul_crossing`,
     `rademacherPhi_crossing_mul`, and `rademacherPhi_crossingMatrix`; they are imported and
     applied below instead of reproving the Dedekind-sum propagation law.
   * Pinned-Mathlib searches for constant-step iterates, arithmetic-progression iterates, and
     unique orbit zeros found no theorem matching the final statement.
   * `Function.Semiconj.iterate_right` is the exact upstream iteration-transport theorem and is
     applied to both the matrix orbit and its winding phase.
-/

namespace D5.S3.PrimeForms.Crossing.WindingOrbitZero

open D5.S3.PrimeForms.Crossing.ExactPropagation

/-- Sandwich a positive matrix between two copies of the fixed crossing matrix. -/
def crossingSandwich (A : PositiveMatrix) : PositiveMatrix :=
  crossingMatrix.mul (A.mul crossingMatrix)

private def PhaseAdmissible (A : PositiveMatrix) : Prop :=
  0 < A.a ∧ 0 < A.c ∧ 0 < A.d ∧ A.a * A.d = A.b * A.c + 1

private theorem mul_crossing_admissible {A : PositiveMatrix} (hA : PhaseAdmissible A) :
    PhaseAdmissible (A.mul crossingMatrix) := by
  rcases hA with ⟨ha, hc, hd, hdet⟩
  simp only [PhaseAdmissible, PositiveMatrix.mul, crossingMatrix]
  refine ⟨by omega, by omega, by omega, ?_⟩
  nlinarith [hdet]

private theorem crossing_mul_admissible {A : PositiveMatrix} (hA : PhaseAdmissible A) :
    PhaseAdmissible (crossingMatrix.mul A) := by
  rcases hA with ⟨ha, hc, hd, hdet⟩
  simp only [PhaseAdmissible, PositiveMatrix.mul, crossingMatrix]
  refine ⟨by omega, by omega, by omega, ?_⟩
  nlinarith [hdet]

private theorem crossing_sandwich_admissible {A : PositiveMatrix} (hA : PhaseAdmissible A) :
    PhaseAdmissible (crossingSandwich A) := by
  exact crossing_mul_admissible (mul_crossing_admissible hA)

private theorem winding_phase_crossing_sandwich {A : PositiveMatrix}
    (hA : PhaseAdmissible A) :
    windingPhase (crossingSandwich A) = windingPhase A - 2 := by
  rcases hA with ⟨ha, hc, hd, hdet⟩
  have hRight := rademacherPhi_mul_crossing A hc hd hdet
  have hAM : PhaseAdmissible (A.mul crossingMatrix) :=
    mul_crossing_admissible ⟨ha, hc, hd, hdet⟩
  have hLeft := rademacherPhi_crossing_mul (A.mul crossingMatrix)
    hAM.1 hAM.2.1 hAM.2.2.1 hAM.2.2.2
  change rademacherPhi (crossingMatrix.mul (A.mul crossingMatrix)) - 3 =
    (rademacherPhi A - 3) - 2
  rw [hLeft, hRight, rademacherPhi_crossingMatrix]
  ring

private abbrev AdmissibleMatrix := {A : PositiveMatrix // PhaseAdmissible A}

private def admissibleSandwich (A : AdmissibleMatrix) : AdmissibleMatrix :=
  ⟨crossingSandwich A.1, crossing_sandwich_admissible A.2⟩

private def admissiblePhase (A : AdmissibleMatrix) : Rat := windingPhase A.1

private theorem admissible_value_semiconj :
    Function.Semiconj (fun A : AdmissibleMatrix => A.1) admissibleSandwich crossingSandwich := by
  intro A
  rfl

private theorem admissible_phase_semiconj :
    Function.Semiconj admissiblePhase admissibleSandwich (fun q : Rat => q - 2) := by
  intro A
  exact winding_phase_crossing_sandwich A.2

private theorem sub_two_iterate (q : Rat) (n : ℕ) :
    ((fun x : Rat => x - 2)^[n]) q = q - 2 * n := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      push_cast
      ring

private theorem winding_phase_crossing_sandwich_iterate
    (A : PositiveMatrix) (hA : PhaseAdmissible A) (n : ℕ) :
    windingPhase ((crossingSandwich^[n]) A) = windingPhase A - 2 * n := by
  let A0 : AdmissibleMatrix := ⟨A, hA⟩
  have hValue := (admissible_value_semiconj.iterate_right n) A0
  have hPhase := (admissible_phase_semiconj.iterate_right n) A0
  change windingPhase (((admissibleSandwich^[n]) A0).1) =
    ((fun q : Rat => q - 2)^[n]) (windingPhase A) at hPhase
  rw [hValue, sub_two_iterate] at hPhase
  exact hPhase

/-- If an admissible positive matrix starts at the even winding phase `2k`, repeatedly
sandwiching it by `[[3,1],[2,1]]` reaches winding phase zero exactly at step `k`. -/
theorem sandwich_orbit_has_unique_winding_zero
    (A : PositiveMatrix)
    (ha : 0 < A.a) (hc : 0 < A.c) (hd : 0 < A.d)
    (hdet : A.a * A.d = A.b * A.c + 1)
    (k : ℕ) (hphase : windingPhase A = 2 * k) :
    ∃! n : ℕ, windingPhase ((crossingSandwich^[n]) A) = 0 := by
  have hA : PhaseAdmissible A := ⟨ha, hc, hd, hdet⟩
  refine ⟨k, ?_, ?_⟩
  · change windingPhase ((crossingSandwich^[k]) A) = 0
    rw [winding_phase_crossing_sandwich_iterate A hA, hphase]
    ring
  · intro n hn
    change windingPhase ((crossingSandwich^[n]) A) = 0 at hn
    rw [winding_phase_crossing_sandwich_iterate A hA, hphase] at hn
    have hcast : (n : Rat) = k := by linarith
    exact_mod_cast hcast

#print axioms sandwich_orbit_has_unique_winding_zero

end D5.S3.PrimeForms.Crossing.WindingOrbitZero
