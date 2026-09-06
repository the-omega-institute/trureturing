/- GID: D5/S3/Quantum/WeylChronology/ClosedPathChronologyAmbiguity
   generality: G
   mirror-B: none(waiver:candidate-audit)
   mirror-E: none(waiver:analytic-necessary-condition)
   anchors: []
   digest: Exact endpoint closure leaves a sharply bounded differential phase that can erase chronology. -/

import D5.S3.Quantum.WeylChronology.SymmetricGaussianCompensation

/-!
# Sharp ambiguity from closed but mismatched compensation

This is an audit of the existing control architecture, not a claimed solution of
an external open problem or a new Weyl identity. The preregistered question is in
PR #5750 comment 5558943192. The matched-half theorem retains its premise.

If the pre/post errors are h and -h, the residual displacement is zero but the
real phase is Y*hx-X*hy. An explicit perpendicular error vector attains the
Cauchy bound, hence the exact minimum squared half-error for a prescribed real
phase eta is eta^2/(X^2+Y^2). The resulting ambiguity witnesses are actual
wavefunction-action equalities, not only collisions of a selected statistic.

Two hypotheses may have DIFFERENT nuisance records, as in the existing
run-to-run uncertainty model. This is not a no-go theorem for a single shared
nuisance, simultaneous reference calibration, adaptive control, or different
settings. Phase-budget equivalences below concern unwrapped real phases;
periodic aliases may create additional ambiguities and are not excluded.

Source audit: current dev 875a09bb61a2288003d224247ef8a7c7935e1df0;
parent stack dff43c8fe8cf16fa83bfacdda22090fd682acc61. #5821 already supplies
the generic ordered-moment/Magnus formula. No replacement moment or Gaussian
owner is introduced. Loning's finite reference-channel fidelity is a different
observable and is not treated as Ramsey visibility.

Physical comparison: Zhang et al., QST 10,035009 (2025), arXiv:2501.02847;
Zlatanov et al., PRApplied 25,034069 (2026), doi:10.1103/66qf-fjy1.
These already separate residual-motion and phase errors. No experimental or
priority claim is made for the algebraic failure mode isolated here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.ClosedPathChronologyAmbiguity

open D5.S1.Words
open D5.S3.Quantum.WeylChronology.SchrodingerDisplacement
open D5.S3.Quantum.WeylChronology.SymmetricGaussianCompensation
open D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge
open D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery

noncomputable section

/-- Perpendicular half-error attaining a prescribed unwrapped phase. -/
def phaseErrorVector (X Y eta : ℝ) : ℝ × ℝ :=
  (eta * Y / (X ^ 2 + Y ^ 2), -eta * X / (X ^ 2 + Y ^ 2))

/-- Anti-matched errors close the displacement but leave a symplectic phase. -/
theorem closed_error_phase (X Y hx hy : ℝ) :
    splitPhase X Y hx hy (-hx) (-hy) = Y * hx - X * hy := by
  unfold splitPhase
  ring

/-- The exact two-dimensional Lagrange remainder gives a sharp energy bound. -/
theorem closed_phase_energy_identity (X Y hx hy : ℝ) :
    (X ^ 2 + Y ^ 2) * (hx ^ 2 + hy ^ 2) -
      (splitPhase X Y hx hy (-hx) (-hy)) ^ 2 = (X * hx + Y * hy) ^ 2 := by
  rw [closed_error_phase]
  ring

/-- The phase cannot exceed the endpoint norm times the half-error norm. -/
theorem closed_phase_energy_bound (X Y hx hy : ℝ) :
    (splitPhase X Y hx hy (-hx) (-hy)) ^ 2 ≤
      (X ^ 2 + Y ^ 2) * (hx ^ 2 + hy ^ 2) := by
  have h := closed_phase_energy_identity X Y hx hy
  nlinarith [sq_nonneg (X * hx + Y * hy)]

/-- The constructed vector attains the bound and realizes the requested phase. -/
theorem phase_error_vector_exact (X Y eta : ℝ) (hD : 0 < X ^ 2 + Y ^ 2) :
    splitPhase X Y (phaseErrorVector X Y eta).1 (phaseErrorVector X Y eta).2
      (-(phaseErrorVector X Y eta).1) (-(phaseErrorVector X Y eta).2) = eta ∧
    (phaseErrorVector X Y eta).1 ^ 2 + (phaseErrorVector X Y eta).2 ^ 2 =
      eta ^ 2 / (X ^ 2 + Y ^ 2) := by
  have hne : X ^ 2 + Y ^ 2 ≠ 0 := ne_of_gt hD
  constructor
  · rw [closed_error_phase]
    dsimp [phaseErrorVector]
    field_simp [hne] <;> ring
  · dsimp [phaseErrorVector]
    field_simp [hne] <;> ring

/-- Exact attainability threshold for a closed-loop real phase with squared budget R. -/
theorem bounded_closed_phase_iff (X Y eta R : ℝ) (hD : 0 < X ^ 2 + Y ^ 2) :
    (∃ hx hy : ℝ, hx ^ 2 + hy ^ 2 ≤ R ∧
      splitPhase X Y hx hy (-hx) (-hy) = eta) ↔
      eta ^ 2 ≤ (X ^ 2 + Y ^ 2) * R := by
  constructor
  · rintro ⟨hx, hy, hnorm, hphase⟩
    have h := (closed_phase_energy_bound X Y hx hy).trans
      (mul_le_mul_of_nonneg_left hnorm hD.le)
    simpa only [hphase] using h
  · intro h
    have hv := phase_error_vector_exact X Y eta hD
    refine ⟨(phaseErrorVector X Y eta).1, (phaseErrorVector X Y eta).2, ?_, hv.1⟩
    rw [hv.2]
    exact (div_le_iff₀ hD).mpr (by nlinarith [h])

/-- A closed erroneous experiment acts by a pure phase on EVERY input function. -/
theorem closed_error_word_normal_form (a b hx hy : ℝ)
    (word : List Bool) (f : ℝ → ℂ) :
    splitCompensatedWord a b hx hy (-hx) (-hy) word f =
      Complex.exp (((a * b * (magnusCenter word : ℝ) +
        splitPhase (a * word.count true) (b * word.count false) hx hy (-hx) (-hy) : ℝ) : ℂ) *
          Complex.I) • f := by
  rw [split_compensation_normal_form]
  simp only [add_neg_cancel]
  have hz : displacement 0 0 f = f := by
    funext q
    simp [displacement]
  rw [hz]

/-- Sharp collision threshold for two unwrapped phases at the same endpoint.
Each hypothesis has its own closed error record with the same squared budget. -/
theorem bounded_real_phase_collision_iff (X Y alpha beta R : ℝ)
    (hD : 0 < X ^ 2 + Y ^ 2) :
    (∃ hx hy kx ky : ℝ,
      hx ^ 2 + hy ^ 2 ≤ R ∧ kx ^ 2 + ky ^ 2 ≤ R ∧
      alpha + splitPhase X Y hx hy (-hx) (-hy) =
        beta + splitPhase X Y kx ky (-kx) (-ky)) ↔
      (beta - alpha) ^ 2 ≤ 4 * (X ^ 2 + Y ^ 2) * R := by
  constructor
  · rintro ⟨hx, hy, kx, ky, hh, hk, heq⟩
    have hp := (closed_phase_energy_bound X Y hx hy).trans
      (mul_le_mul_of_nonneg_left hh hD.le)
    have hq := (closed_phase_energy_bound X Y kx ky).trans
      (mul_le_mul_of_nonneg_left hk hD.le)
    nlinarith [sq_nonneg (splitPhase X Y hx hy (-hx) (-hy) +
      splitPhase X Y kx ky (-kx) (-ky))]
  · intro h
    have hhalf : ((beta - alpha) / 2) ^ 2 ≤ (X ^ 2 + Y ^ 2) * R := by
      nlinarith [h]
    obtain ⟨hx, hy, hn, hp⟩ :=
      (bounded_closed_phase_iff X Y ((beta - alpha) / 2) R hD).mpr hhalf
    refine ⟨hx, hy, -hx, -hy, hn, ?_, ?_⟩
    · simpa only [neg_sq] using hn
    · rw [closed_error_phase] at hp ⊢
      rw [closed_error_phase]
      linarith

/-- Equal inventories admit identical complete actions once the sharp real-phase
budget is crossed. Increasing shots at this fixed setting cannot distinguish
these constructed nuisance records. No shared-nuisance claim is made. -/
theorem same_inventory_bounded_action_collision (a b R : ℝ) (left right : List Bool)
    (htrue : left.count true = right.count true)
    (hfalse : left.count false = right.count false)
    (hD : 0 < (a * left.count true) ^ 2 + (b * left.count false) ^ 2)
    (hbudget : (a * b * ((magnusCenter right : ℝ) - (magnusCenter left : ℝ))) ^ 2 ≤
      4 * ((a * left.count true) ^ 2 + (b * left.count false) ^ 2) * R) :
    ∃ hx hy kx ky : ℝ,
      hx ^ 2 + hy ^ 2 ≤ R ∧ kx ^ 2 + ky ^ 2 ≤ R ∧
      ∀ f : ℝ → ℂ,
        splitCompensatedWord a b hx hy (-hx) (-hy) left f =
          splitCompensatedWord a b kx ky (-kx) (-ky) right f := by
  have hphaseBudget : (a * b * (magnusCenter right : ℝ) -
      a * b * (magnusCenter left : ℝ)) ^ 2 ≤
      4 * ((a * left.count true) ^ 2 + (b * left.count false) ^ 2) * R := by
    nlinarith [hbudget]
  obtain ⟨hx, hy, kx, ky, hh, hk, heq⟩ :=
    (bounded_real_phase_collision_iff (a * left.count true) (b * left.count false)
      (a * b * (magnusCenter left : ℝ)) (a * b * (magnusCenter right : ℝ)) R hD).mpr hphaseBudget
  refine ⟨hx, hy, kx, ky, hh, hk, ?_⟩
  intro f
  rw [closed_error_word_normal_form, closed_error_word_normal_form, ← htrue, ← hfalse]
  exact congrArg (fun angle : ℝ => Complex.exp ((angle : ℂ) * Complex.I) • f) heq

/-- The actual legal LSLL and LLSL factors can coincide as full actions.
The exact squared budget per half is a^2/10, for equal nonzero amplitudes a.
This is a failure certificate for a broader error class, not a refutation of
the earlier theorem whose two errors were required to match. -/
theorem distinct_legal_factors_closed_action_collision (a : ℝ) (ha : a ≠ 0) :
    goldenFactor 4 0 ≠ goldenFactor 4 2 ∧
      ∃ hx hy kx ky : ℝ,
        hx ^ 2 + hy ^ 2 ≤ a ^ 2 / 10 ∧ kx ^ 2 + ky ^ 2 ≤ a ^ 2 / 10 ∧
        ∀ f : ℝ → ℂ,
          splitCompensatedWord a a hx hy (-hx) (-hy) (goldenFactor 4 0) f =
            splitCompensatedWord a a kx ky (-kx) (-ky) (goldenFactor 4 2) f := by
  have hleft : goldenFactor 4 0 = [true, false, true, true] := by decide
  have hright : goldenFactor 4 2 = [true, true, false, true] := by decide
  rw [hleft, hright]
  refine ⟨by decide, ?_⟩
  apply same_inventory_bounded_action_collision a a (a ^ 2 / 10)
  · decide
  · decide
  · norm_num <;> nlinarith [sq_pos_of_ne_zero ha]
  · norm_num [magnus_center_formula, scatteredTrueFalseCount] <;> nlinarith [sq_nonneg a]

#print axioms bounded_closed_phase_iff
#print axioms bounded_real_phase_collision_iff
#print axioms same_inventory_bounded_action_collision
#print axioms distinct_legal_factors_closed_action_collision

end
end D5.S3.Quantum.WeylChronology.ClosedPathChronologyAmbiguity
