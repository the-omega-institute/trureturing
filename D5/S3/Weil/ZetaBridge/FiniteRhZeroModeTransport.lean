/- GID: D5/S3/Weil/ZetaBridge/FiniteRhZeroModeTransport
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/FiniteRhZeroModeTransport
   mirror-E: none(waiver:conditional-rh-finite-transport-only)
   anchors: []
   digest: Finite families of supplied zero characters form reversible diagonal transports, and RH makes every transported coordinate norm preserving. -/

import D5.S3.Weil.ZetaBridge.RhZeroModeUnitarity

/-!
A finite selector chooses supplied nontrivial zero indices. Their existing
log-scale characters act diagonally on finite amplitude families. Character
multiplication gives a reversible real-time action without RH. The conditional
RH bridge then removes every radial norm change coordinatewise. This remains a
finite character model and does not construct a completed-xi spectral operator.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.FiniteRhZeroModeTransport

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.RhZeroModeUnitarity
open D5.S3.Weil.ZetaLinear.OfflineZeroCharacter

/-- Diagonal real-time transport by a finite selected family of supplied zero
characters. -/
def finiteZeroModeTransport {m : ℕ}
    (Z : ZeroData) (indices : Fin m → ℕ) (time : ℝ)
    (amplitudes : Fin m → ℂ) : Fin m → ℂ :=
  fun mode =>
    offlineZeroCharacter (Z.zero (indices mode))
        (Multiplicative.ofAdd time) * amplitudes mode

/-- Zero elapsed time is the identity transport. -/
@[simp] theorem finite_zero_mode_transport_zero {m : ℕ}
    (Z : ZeroData) (indices : Fin m → ℕ) (amplitudes : Fin m → ℂ) :
    finiteZeroModeTransport Z indices 0 amplitudes = amplitudes := by
  funext mode
  simp [finiteZeroModeTransport]

/-- Successive selected-zero transports compose by addition of real times. -/
theorem finite_zero_mode_transport_add {m : ℕ}
    (Z : ZeroData) (indices : Fin m → ℕ) (first second : ℝ)
    (amplitudes : Fin m → ℂ) :
    finiteZeroModeTransport Z indices (first + second) amplitudes =
      finiteZeroModeTransport Z indices first
        (finiteZeroModeTransport Z indices second amplitudes) := by
  funext mode
  change
    offlineZeroCharacter (Z.zero (indices mode))
        (Multiplicative.ofAdd (first + second)) * amplitudes mode =
      offlineZeroCharacter (Z.zero (indices mode))
          (Multiplicative.ofAdd first) *
        (offlineZeroCharacter (Z.zero (indices mode))
            (Multiplicative.ofAdd second) * amplitudes mode)
  rw [show Multiplicative.ofAdd (first + second) =
      Multiplicative.ofAdd first * Multiplicative.ofAdd second by rfl]
  rw [map_mul]
  exact mul_assoc _ _ _

/-- Negative time is an inverse for every finite selected-zero transport. -/
theorem finite_zero_mode_transport_neg_left {m : ℕ}
    (Z : ZeroData) (indices : Fin m → ℕ) (time : ℝ)
    (amplitudes : Fin m → ℂ) :
    finiteZeroModeTransport Z indices (-time)
        (finiteZeroModeTransport Z indices time amplitudes) = amplitudes := by
  have h := finite_zero_mode_transport_add Z indices (-time) time amplitudes
  simpa using h.symm

/-- Under RH, every coordinate norm is invariant under the finite selected-zero
transport. -/
theorem finite_rh_zero_mode_transport_coordinate_norm {m : ℕ}
    (hRH : RiemannHypothesis) (Z : ZeroData) (indices : Fin m → ℕ)
    (time : ℝ) (amplitudes : Fin m → ℂ) (mode : Fin m) :
    ‖finiteZeroModeTransport Z indices time amplitudes mode‖ =
      ‖amplitudes mode‖ := by
  rw [finiteZeroModeTransport, norm_mul,
    rh_zero_mode_norm_one hRH Z (indices mode) time, one_mul]

/-- The finite model separates unconditional reversibility from conditional
unitarity: the action law and inverse hold for every supplied zero family, while
RH supplies coordinatewise norm preservation. -/
theorem finite_rh_zero_mode_transport
    {m : ℕ} (hRH : RiemannHypothesis) (Z : ZeroData)
    (indices : Fin m → ℕ) (first second : ℝ)
    (amplitudes : Fin m → ℂ) :
    finiteZeroModeTransport Z indices 0 amplitudes = amplitudes ∧
    finiteZeroModeTransport Z indices (first + second) amplitudes =
      finiteZeroModeTransport Z indices first
        (finiteZeroModeTransport Z indices second amplitudes) ∧
    finiteZeroModeTransport Z indices (-first)
        (finiteZeroModeTransport Z indices first amplitudes) = amplitudes ∧
    ∀ mode,
      ‖finiteZeroModeTransport Z indices first amplitudes mode‖ =
        ‖amplitudes mode‖ :=
  ⟨finite_zero_mode_transport_zero Z indices amplitudes,
    finite_zero_mode_transport_add Z indices first second amplitudes,
    finite_zero_mode_transport_neg_left Z indices first amplitudes,
    finite_rh_zero_mode_transport_coordinate_norm hRH Z indices first amplitudes⟩

#print axioms finite_zero_mode_transport_zero
#print axioms finite_zero_mode_transport_add
#print axioms finite_zero_mode_transport_neg_left
#print axioms finite_rh_zero_mode_transport_coordinate_norm
#print axioms finite_rh_zero_mode_transport

end D5.S3.Weil.ZetaBridge.FiniteRhZeroModeTransport
