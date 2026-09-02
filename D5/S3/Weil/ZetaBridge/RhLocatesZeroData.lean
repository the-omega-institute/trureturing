/- GID: D5/S3/Weil/ZetaBridge/RhLocatesZeroData
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/RhLocatesZeroData
   mirror-E: none(waiver:conditional-critical-line-bridge-only)
   anchors: []
   digest: Under RH, every supplied ZeroData zero lies on the critical line. -/

import D5.S3.Weil.ZetaCore.Statement
import D5.S3.Weil.ZeroSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.RhLocatesZeroData

open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum

/-!
This module realizes route R-E by composing the frozen `ZeroData`
nontrivial-zero witness with the frozen `Zeta23.RH_implies_on_line` theorem.
The latter already excludes the trivial zeros and the pole at one.

The result is conditional on Mathlib's `RiemannHypothesis`. It does not prove
RH, O-6, or any zero-counting statement. Its R-F consumer is a one-line
composition with this bridge.
-/

/-- Under Mathlib's Riemann hypothesis, every zero in supplied `ZeroData` lies
on the critical line. -/
theorem zeroData_zero_on_critical_line_of_rh
    (hRH : RiemannHypothesis)
    (Z : ZeroData)
    (n : ℕ) :
    (Z.zero n).re = criticalAbscissa := by
  have h : Zeta23.IsNontrivialZero (Z.zero n) := Z.zero_isNontrivial n
  unfold criticalAbscissa
  exact Zeta23.RH_implies_on_line hRH h

-- The conditional hypothesis context is jointly witnessable by its binders.
example (hRH : RiemannHypothesis) (Z : ZeroData) (n : ℕ) :
    RiemannHypothesis ∧ Nonempty ZeroData ∧ Nonempty ℕ :=
  ⟨hRH, ⟨Z⟩, ⟨n⟩⟩

-- The quantified index domain has a closed inhabitant.
example : Nonempty ℕ := ⟨0⟩

#print axioms zeroData_zero_on_critical_line_of_rh

end D5.S3.Weil.ZetaBridge.RhLocatesZeroData
