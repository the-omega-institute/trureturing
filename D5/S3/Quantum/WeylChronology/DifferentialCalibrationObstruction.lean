/- GID: D5/S3/Quantum/WeylChronology/DifferentialCalibrationObstruction
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:exact-control-identifiability)
   anchors: []
   digest: Perfect endpoint closure permits chronology aliases under bounded differential compensation errors. -/

import D5.S3.Quantum.WeylChronology.SymmetricGaussianCompensation

/-!
# Differential calibration is an identifiability obstruction

The source consumes the existing literal splitCompensatedWord action.
Opposite pre/post errors close the endpoint exactly but retain the central
phase Y*ux-X*uy. The construction below determines the exact squared-radius
condition for an unwrapped two-record phase alias and transports it to equality
of the completed actions on all input wavefunctions.

Scope: fixed common inventory, observation of completed actions, fixed additive
half-error balls, and unwrapped real phases. The converse radius theorem does
not rule out additional aliases modulo 2*pi. No experimental advantage, full
noise model, independent review or successful Lean build is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.DifferentialCalibrationObstruction

open D5.S3.Quantum.WeylChronology.SchrodingerDisplacement
open D5.S3.Quantum.WeylChronology.SymmetricGaussianCompensation
open D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery

noncomputable section

/-- Zero total displacement does not imply zero central error. -/
theorem zero_total_error_phase (X Y ux uy : ℝ) :
    splitPhase X Y ux uy (-ux) (-uy) = Y * ux - X * uy := by
  unfold splitPhase
  ring

private theorem phase_cauchy (X Y ux uy : ℝ) :
    (Y * ux - X * uy) ^ 2 ≤ (X ^ 2 + Y ^ 2) * (ux ^ 2 + uy ^ 2) := by
  nlinarith [sq_nonneg (X * ux + Y * uy)]

/-- Exact phase radius, with an explicit attaining error vector. -/
theorem zero_total_phase_radius_iff (X Y angle radius : ℝ)
    (hendpoint : 0 < X ^ 2 + Y ^ 2) :
    (∃ ux uy : ℝ, ux ^ 2 + uy ^ 2 ≤ radius ^ 2 ∧
      splitPhase X Y ux uy (-ux) (-uy) = angle) ↔
      angle ^ 2 ≤ radius ^ 2 * (X ^ 2 + Y ^ 2) := by
  constructor
  · rintro ⟨ux, uy, hnorm, hphase⟩
    rw [zero_total_error_phase] at hphase
    have hc := phase_cauchy X Y ux uy
    have hb := mul_le_mul_of_nonneg_left hnorm hendpoint.le
    rw [hphase] at hc
    nlinarith
  · intro hangle
    let R : ℝ := X ^ 2 + Y ^ 2
    have hR : 0 < R := hendpoint
    have hRne : R ≠ 0 := hR.ne'
    refine ⟨angle * Y / R, -(angle * X / R), ?_, ?_⟩
    · have hnorm : (angle * Y / R) ^ 2 + (-(angle * X / R)) ^ 2 =
          angle ^ 2 / R := by
        dsimp only [R] at hRne ⊢
        field_simp [hRne] <;> ring
      rw [hnorm]
      apply (div_le_iff₀ hR).mpr
      exact hangle
    · rw [zero_total_error_phase]
      dsimp only [R] at hRne ⊢
      field_simp [hRne] <;> ring

/-- Sharp unwrapped alias condition when both hypotheses have unknown
admissible records. Periodic phase aliases remain outside the converse. -/
theorem two_record_phase_alias_iff (X Y phaseL phaseR radius : ℝ)
    (hendpoint : 0 < X ^ 2 + Y ^ 2) :
    (∃ ux uy vx vy : ℝ,
      ux ^ 2 + uy ^ 2 ≤ radius ^ 2 ∧
      vx ^ 2 + vy ^ 2 ≤ radius ^ 2 ∧
      phaseL + splitPhase X Y ux uy (-ux) (-uy) =
        phaseR + splitPhase X Y vx vy (-vx) (-vy)) ↔
      (phaseL - phaseR) ^ 2 ≤ 4 * radius ^ 2 * (X ^ 2 + Y ^ 2) := by
  constructor
  · rintro ⟨ux, uy, vx, vy, hu, hv, hphase⟩
    simp only [zero_total_error_phase] at hphase
    have hdiff : (ux-vx)^2 + (uy-vy)^2 ≤ 4 * radius ^ 2 := by
      nlinarith [sq_nonneg (ux+vx), sq_nonneg (uy+vy)]
    have hc := phase_cauchy X Y (ux-vx) (uy-vy)
    have hb := mul_le_mul_of_nonneg_left hdiff hendpoint.le
    have heq : phaseL - phaseR = -(Y*(ux-vx)-X*(uy-vy)) := by
      nlinarith [hphase]
    rw [heq]
    nlinarith [hc, hb]
  · intro hgap
    have hhalf : ((phaseR-phaseL)/2)^2 ≤ radius^2*(X^2+Y^2) := by
      nlinarith [hgap]
    obtain ⟨ux, uy, hu, hphase⟩ :=
      (zero_total_phase_radius_iff X Y ((phaseR-phaseL)/2) radius hendpoint).mpr hhalf
    refine ⟨ux, uy, -ux, -uy, hu, ?_, ?_⟩
    · simpa only [neg_sq] using hu
    · simp only [zero_total_error_phase] at hphase ⊢
      nlinarith [hphase]

/-- The actual action closes perfectly while its phase remains error dependent. -/
theorem zero_total_control_normal_form (a b ux uy : ℝ)
    (word : List Bool) (f : ℝ → ℂ) :
    splitCompensatedWord a b ux uy (-ux) (-uy) word f =
      Complex.exp (((a*b*(magnusCenter word : ℝ) +
        (b*(word.count false : ℝ))*ux - (a*(word.count true : ℝ))*uy : ℝ) : ℂ) *
          Complex.I) • f := by
  rw [split_compensation_normal_form, zero_total_error_phase]
  simp only [add_neg_cancel]
  have hid : displacement 0 0 f = f := by
    funext q
    simp [displacement]
  rw [hid]
  have he : a*b*(magnusCenter word : ℝ) +
      ((b*(word.count false : ℝ))*ux - (a*(word.count true : ℝ))*uy) =
      a*b*(magnusCenter word : ℝ) + (b*(word.count false : ℝ))*ux -
        (a*(word.count true : ℝ))*uy := by ring
  rw [he]

/-- Exact alias of completed operators, with zero net residual in both records. -/
theorem closed_endpoint_operator_alias
    (a b radius : ℝ) (left right : List Bool)
    (htrue : left.count true = right.count true)
    (hfalse : left.count false = right.count false)
    (hendpoint : 0 < (a*(left.count true : ℝ))^2 + (b*(left.count false : ℝ))^2)
    (hgap : (a*b*((magnusCenter left : ℝ)-(magnusCenter right : ℝ)))^2 ≤
      4*radius^2*((a*(left.count true : ℝ))^2+(b*(left.count false : ℝ))^2)) :
    ∃ ux uy vx vy : ℝ,
      ux^2+uy^2 ≤ radius^2 ∧ vx^2+vy^2 ≤ radius^2 ∧
      ∀ f : ℝ → ℂ,
        splitCompensatedWord a b ux uy (-ux) (-uy) left f =
        splitCompensatedWord a b vx vy (-vx) (-vy) right f := by
  have hgap' : (a*b*(magnusCenter left : ℝ)-a*b*(magnusCenter right : ℝ))^2 ≤
      4*radius^2*((a*(left.count true : ℝ))^2+(b*(left.count false : ℝ))^2) := by
    convert hgap using 1 <;> ring
  obtain ⟨ux, uy, vx, vy, hu, hv, hphase⟩ :=
    (two_record_phase_alias_iff (a*(left.count true : ℝ))
      (b*(left.count false : ℝ)) (a*b*(magnusCenter left : ℝ))
      (a*b*(magnusCenter right : ℝ)) radius hendpoint).mpr hgap'
  refine ⟨ux, uy, vx, vy, hu, hv, ?_⟩
  intro f
  rw [zero_total_control_normal_form, zero_total_control_normal_form,
    ← htrue, ← hfalse]
  have he : a*b*(magnusCenter left : ℝ)+(b*(left.count false : ℝ))*ux-
      (a*(left.count true : ℝ))*uy =
      a*b*(magnusCenter right : ℝ)+(b*(left.count false : ℝ))*vx-
        (a*(left.count true : ℝ))*vy := by
    simp only [zero_total_error_phase] at hphase
    nlinarith [hphase]
  rw [he]

#print axioms zero_total_phase_radius_iff
#print axioms two_record_phase_alias_iff
#print axioms closed_endpoint_operator_alias

end
end D5.S3.Quantum.WeylChronology.DifferentialCalibrationObstruction
