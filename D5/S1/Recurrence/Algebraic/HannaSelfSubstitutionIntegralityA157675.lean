/- GID: D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegralityA157675
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegralityA157675
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's A157675 self-substitution series has integer coefficients. -/

/-
admission_basis: open-problem-resolution (#18710; Proved)
escape_witness: none; admission uses the external settling result.
claim: proof_shape: definition; escape_witness: none; consumers: result; Direct frozen dependencies: F17.
result: proof_shape: content; escape_witness: none; consumers: external settlement; Direct frozen dependencies: F17, F8, F28, F18, F27, F16, F22, F5, F3, F1, F15, F13, F31, F40, F39, F30, F23, F24, F25, F21.
Direct frozen dependencies:
F1: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.IsRIntegralPS; statement_id: sha256:ba8f837cf22cb5e9c10e6b49f31c6bc2b100067357955e0c6fe55384a0750ea9.
F3: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.IsRIntegralRat; statement_id: sha256:53246f9f06573c4281b2b5f6125688d166229f662aea17c390eb7f72caae7aa3.
F5: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.local_integral_sum; statement_id: sha256:67b906f1feddcd8598a952e1c78597056ae3ced10cae8193e56c1663b3bf7bbb.
F8: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.expSeries_constant; statement_id: sha256:3818db27ec0992d51a03df5086b6f167ef61cc182ed886b9fca617d13755f428.
F13: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.integral_of_local; statement_id: sha256:de14e85f34e107074880cc1c807c785cfb3232dbda7341ae542622678962c4e4.
F15: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.local_exp_of_log_difference; statement_id: sha256:457327474b89982dc4eaa0999fd690ca2e73f9fe6bccce56c22322e3521b9f70.
F16: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.local_int_div_nat; statement_id: sha256:e96240d98b9b17063b4d23bfa79fa67607f88687ff543bdfc489a8cd0b414af0.
F17: D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.IntegralSeries; statement_id: sha256:63e70f464749e368856bfaa91133b0adfeda478327572310319dbf6077b632cb.
F18: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.prime_power_subst; statement_id: sha256:4b665513911f58443c7679757dc619d66730344174351ea1f23cedc92766f795.
F21: D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed; statement_id: sha256:bd62df5aa141eaff1ceec9e8af00309b4a8e194b4354ad180a51862599cef981.
F22: D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.map_subst_pow; statement_id: sha256:d19dcfba5fe44ddf479cc0294b8857874dc3c678681b9b22b3f1dfa5ddc1c7cd.
F23: D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree; statement_id: sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34.
F24: D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_pow; statement_id: sha256:0c9456bb3300b1f38308df2b3a2abc2d51d68b3b05356990e7bc5cfc4bfb0dbb.
F25: D5/S1/Recurrence/Invariants/UnitReversionSquareParity.subst_inner_agree; statement_id: sha256:70b2ee35c9f37a83ac3c7fafdd24ab8c9a71bd427dd766a52b2641e8e37ecfa5.
F27: D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.C_dvd_iff_coeff; statement_id: sha256:8c1882146ae6e181a5d76db021c447d3d876e2310da5375697c52f0bb35ef4a1.
F28: D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.linear_ode_unique; statement_id: sha256:3ee42d0d09e04d4498194d296af5f0f5a145cdae9192b759e0c6e4174d652ebe.
F30: D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.divisorGhost; statement_id: sha256:27f83da21eae9f4f50072fef77b1af6f5c3425852cd01eaff663bcfa02d0dd04.
F31: D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.divisor_ghost_gauss; statement_id: sha256:ee871fe21a8444af72ab71b5e6400a07ffe1efea286c857e4a104a0db9045cae.
F39: D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.integral_input_ledger; statement_id: sha256:bf3d7b524710191f707c7b1a65af5a365e89f916b533f1f58d0ce2ddf9fc39e8.
F40: D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.logarithmicInput; statement_id: sha256:b5bd1729420ea137fa187a9a0e1d88b1b77aaf96af596fd62dcfe2f59419635b.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24041.
-/

import D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality
import D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegralityA157675

open D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality (SolvesHanna)
open D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure (IntegralSeries)

/-- OEIS A157675: "G.f.: A(x) = exp( Sum_{n>=1} A(2^n*x)^n * x^n/n )."
The comment is "Conjectured to consist entirely of integers." -/
def claim : Prop :=
  (∃ A, SolvesHanna (fun n => (2 : ℚ) ^ n) A) ∧
    ∀ A, SolvesHanna (fun n => (2 : ℚ) ^ n) A → IntegralSeries A

theorem result : claim := by
  exact HannaSelfSubstitutionIntegrality.result _
    (HannaSelfSubstitutionIntegrality.geometric_input 2)

end D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegralityA157675
