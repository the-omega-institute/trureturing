/- GID: D5/S3/Weil/ZetaLinear/OfflineZeroCharacter
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaLinear/OfflineZeroCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Realize offline-zero parameters as nonunitary log-scale characters. -/

import D5.S3.Weil.ZetaLinear.ReflectedZeroModePhaseFlattening
import Mathlib.Algebra.Exact.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/- Library-search audit trail (2026-09-01):
   * Repository searches for continuous complex characters, Mellin modes,
     critical displacement, normalized zero modes, and imaginary-axis exact
     sequences found the radial-phase results in
     `ReflectedZeroModePhaseFlattening`, but no bundled log-scale character or
     parameter-space short exact sequence. The mode factorization below is
     therefore transported from that frozen module through its same-height
     critical-line mirror.
   * Pinned Mathlib supplies `ContinuousMonoidHom`, `Complex.exp_add`,
     `Complex.exp_ne_zero`, `Complex.norm_exp`, `Complex.reCLM`, and
     `Function.Exact`; it has no theorem classifying all continuous
     characters from the additive real line to the nonzero complex numbers.
   * A search of the admissible third-party Lean ecosystem found no reusable
     formalization of that classification. This module parameterizes and
     realizes the Mellin family required here, without asserting the absent
     universal classification theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaLinear.OfflineZeroCharacter

open D5.S3.Weil.Convention
open D5.S3.Weil.ZetaLinear.ReflectedZeroModePhaseFlattening

/-- Continuous complex characters on log-scale time, whose multiplication is
addition of real times. -/
abbrev LogScaleCharacter := ContinuousMonoidHom (Multiplicative ℝ) ℂ

/-- The complex plane is the parameter space for the Mellin character family. -/
abbrev CharacterParameter := ℂ

/-- The character with exponent `s`, evaluated as `t ↦ exp (s t)`. -/
def mellinCharacter (s : CharacterParameter) : LogScaleCharacter where
  toFun time := Complex.exp (s * ((time.toAdd : ℝ) : ℂ))
  map_one' := by simp
  map_mul' x y := by
    simp [mul_add, Complex.exp_add]
  continuous_toFun :=
    Complex.continuous_exp.comp
      (continuous_const.mul
        (Complex.continuous_ofReal.comp continuous_toAdd))

@[simp]
theorem mellin_character_apply (s : CharacterParameter) (time : ℝ) :
    mellinCharacter s (Multiplicative.ofAdd time) =
      Complex.exp (s * (time : ℂ)) :=
  rfl

/-- Mellin characters never meet the zero of the ambient complex monoid. -/
theorem mellin_character_ne_zero (s : CharacterParameter) (time : ℝ) :
    mellinCharacter s (Multiplicative.ofAdd time) ≠ 0 := by
  simp

/-- A character is unitary when every real-time value has unit norm. -/
def IsUnitary (chi : LogScaleCharacter) : Prop :=
  ∀ time : ℝ, ‖chi (Multiplicative.ofAdd time)‖ = 1

/-- The radial rate of a Mellin character is the real part of its exponent. -/
theorem mellin_character_norm (s : CharacterParameter) (time : ℝ) :
    ‖mellinCharacter s (Multiplicative.ofAdd time)‖ =
      Real.exp (s.re * time) := by
  simp [Complex.norm_exp]

/-- A Mellin character is unitary exactly on the imaginary parameter axis. -/
theorem mellin_character_unitary_iff (s : CharacterParameter) :
    IsUnitary (mellinCharacter s) ↔ s.re = 0 := by
  constructor
  · intro h
    have hOne := h 1
    rw [mellin_character_norm] at hOne
    rw [Real.exp_eq_one_iff] at hOne
    simpa using hOne
  · intro hs time
    rw [mellin_character_norm, hs, zero_mul, Real.exp_zero]

/-- The exponent attached to an offline zero `rho`. -/
def offlineZeroParameter (rho : ℂ) : CharacterParameter :=
  rho - (criticalAbscissa : ℂ)

/-- The log-scale Mellin character attached to an offline zero parameter. -/
def offlineZeroCharacter (rho : ℂ) : LogScaleCharacter :=
  mellinCharacter (offlineZeroParameter rho)

@[simp]
theorem offline_zero_character_apply (rho : ℂ) (time : ℝ) :
    offlineZeroCharacter rho (Multiplicative.ofAdd time) =
      Complex.exp ((rho - (criticalAbscissa : ℂ)) * (time : ℂ)) :=
  rfl

/-- The same-height critical-line mirror identifies the new character with
the previously frozen normalized zero mode. -/
theorem offline_zero_character_eq_mirrored_mode (rho : ℂ) (time : ℝ) :
    offlineZeroCharacter rho (Multiplicative.ofAdd time) =
      normalizedZeroMode (criticalLineMirror rho) time := by
  change
    Complex.exp ((rho - (criticalAbscissa : ℂ)) * (time : ℂ)) =
      Complex.exp (normalizedZeroGenerator (criticalLineMirror rho) * (time : ℂ))
  have hGenerator :
      rho - (criticalAbscissa : ℂ) =
        normalizedZeroGenerator (criticalLineMirror rho) := by
    apply Complex.ext <;>
      simp [normalizedZeroGenerator, criticalDisplacement, criticalLineMirror,
        criticalAbscissa] <;>
      ring
  rw [hGenerator]

/-- Formula (1128.1): the zero character splits into the radial obstruction
`exp (delta t)` and the unitary phase `exp (i gamma t)`. -/
theorem offline_zero_character_factorization (rho : ℂ) (time : ℝ) :
    offlineZeroCharacter rho (Multiplicative.ofAdd time) =
      Complex.exp (((criticalDisplacement rho * time : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((rho.im * time : ℝ) : ℂ)) := by
  rw [offline_zero_character_eq_mirrored_mode,
    normalized_zero_mode_factorization]
  simp [radialZeroMode, commonZeroPhase]

/-- The horizontal displacement is exactly the real part of the character
parameter. -/
theorem offline_zero_parameter_re (rho : ℂ) :
    (offlineZeroParameter rho).re = criticalDisplacement rho := by
  simp [offlineZeroParameter, criticalDisplacement]

/-- An offline-zero character descends to the unitary axis exactly on the
critical line. -/
theorem offline_zero_character_unitary_iff (rho : ℂ) :
    IsUnitary (offlineZeroCharacter rho) ↔
      rho.re = criticalAbscissa := by
  rw [offlineZeroCharacter, mellin_character_unitary_iff,
    offline_zero_parameter_re]
  exact sub_eq_zero

/-- Nonunitarity is precisely the nonzero descent obstruction `delta`. -/
theorem offline_zero_character_nonunitary_iff (rho : ℂ) :
    ¬IsUnitary (offlineZeroCharacter rho) ↔
      criticalDisplacement rho ≠ 0 := by
  simpa only [criticalDisplacement, sub_ne_zero] using
    not_congr (offline_zero_character_unitary_iff rho)

/-- Inclusion of the imaginary character parameters into the complex
parameter plane. -/
def imaginaryAxisInclusion : ℝ →ₗ[ℝ] ℂ where
  toFun gamma := Complex.I * (gamma : ℂ)
  map_add' x y := by
    apply Complex.ext <;> simp
  map_smul' a x := by
    apply Complex.ext <;> simp

theorem imaginary_axis_inclusion_injective :
    Function.Injective imaginaryAxisInclusion := by
  intro x y h
  have him := congrArg Complex.im h
  simpa [imaginaryAxisInclusion] using him

/-- The imaginary axis is exactly the kernel of the real-part obstruction. -/
theorem imaginary_axis_exact_real_part :
    Function.Exact imaginaryAxisInclusion Complex.reCLM := by
  intro z
  constructor
  · intro hz
    refine ⟨z.im, ?_⟩
    apply Complex.ext
    · simpa [imaginaryAxisInclusion] using hz.symm
    · simp [imaginaryAxisInclusion]
  · rintro ⟨gamma, rfl⟩
    simp [imaginaryAxisInclusion]

theorem real_part_surjective :
    Function.Surjective Complex.reCLM := by
  intro x
  exact ⟨(x : ℂ), by simp⟩

/-- Element-level short exactness of `0 → iℝ → ℂ →Re ℝ → 0`. -/
theorem character_parameter_short_exact :
    Function.Injective imaginaryAxisInclusion ∧
      Function.Exact imaginaryAxisInclusion Complex.reCLM ∧
      Function.Surjective Complex.reCLM :=
  ⟨imaginary_axis_inclusion_injective, imaginary_axis_exact_real_part,
    real_part_surjective⟩

/-- The family is inhabited by a genuinely nonunitary character. -/
theorem exists_nonunitary_offline_zero_character :
    ∃ rho : ℂ, ¬IsUnitary (offlineZeroCharacter rho) := by
  refine ⟨1, ?_⟩
  rw [offline_zero_character_nonunitary_iff]
  norm_num [criticalDisplacement, criticalAbscissa]

#print axioms mellin_character_unitary_iff
#print axioms offline_zero_character_factorization
#print axioms offline_zero_character_nonunitary_iff
#print axioms character_parameter_short_exact
#print axioms exists_nonunitary_offline_zero_character

end D5.S3.Weil.ZetaLinear.OfflineZeroCharacter
