/- GID: D5/S3/Weil/ZetaBridge/RhZeroModeUnitarity
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/RhZeroModeUnitarity
   mirror-E: none(waiver:conditional-rh-character-bridge-only)
   anchors: []
   digest: Under RH, every supplied ZeroData log-scale zero character is unitary and has unit norm at every real transport time. -/

import D5.S3.Weil.ZetaBridge.RhLocatesZeroData
import D5.S3.Weil.ZetaLinear.OfflineZeroCharacter

/-!
This is a conditional composition. `RhLocatesZeroData` puts every supplied
nontrivial zero on the critical line under Mathlib's `RiemannHypothesis`, while
`OfflineZeroCharacter` identifies the critical line with the unitary character
axis. No prime-to-spectrum realization, completed-xi operator, Weil positivity
equivalence, or proof of RH is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.RhZeroModeUnitarity

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.RhLocatesZeroData
open D5.S3.Weil.ZetaLinear.OfflineZeroCharacter

/-- Under RH, the log-scale character attached to every supplied nontrivial
zero is unitary. -/
theorem rh_zero_mode_unitary
    (hRH : RiemannHypothesis) (Z : ZeroData) (n : ℕ) :
    IsUnitary (offlineZeroCharacter (Z.zero n)) := by
  rw [offline_zero_character_unitary_iff]
  exact zeroData_zero_on_critical_line_of_rh hRH Z n

/-- Under RH, all supplied zero modes are unitary simultaneously. -/
theorem rh_all_zero_modes_unitary
    (hRH : RiemannHypothesis) (Z : ZeroData) :
    ∀ n, IsUnitary (offlineZeroCharacter (Z.zero n)) :=
  fun n => rh_zero_mode_unitary hRH Z n

/-- Under RH, every supplied zero-mode multiplier has unit norm at every real
transport time. -/
theorem rh_zero_mode_norm_one
    (hRH : RiemannHypothesis) (Z : ZeroData) (n : ℕ) (time : ℝ) :
    ‖offlineZeroCharacter (Z.zero n) (Multiplicative.ofAdd time)‖ = 1 :=
  rh_zero_mode_unitary hRH Z n time

/-- The conditional RH bridge reaches precisely the unitary transport
observation supplied by the existing character model. -/
theorem rh_zero_mode_observation
    (hRH : RiemannHypothesis) (Z : ZeroData) (n : ℕ) :
    (Z.zero n).re = D5.S3.Weil.Convention.criticalAbscissa ∧
    IsUnitary (offlineZeroCharacter (Z.zero n)) ∧
    ∀ time : ℝ,
      ‖offlineZeroCharacter (Z.zero n) (Multiplicative.ofAdd time)‖ = 1 :=
  ⟨zeroData_zero_on_critical_line_of_rh hRH Z n,
    rh_zero_mode_unitary hRH Z n,
    rh_zero_mode_norm_one hRH Z n⟩

#print axioms rh_zero_mode_unitary
#print axioms rh_all_zero_modes_unitary
#print axioms rh_zero_mode_norm_one
#print axioms rh_zero_mode_observation

end D5.S3.Weil.ZetaBridge.RhZeroModeUnitarity
