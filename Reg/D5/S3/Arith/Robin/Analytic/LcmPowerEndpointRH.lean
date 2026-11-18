import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.LcmPowerEndpointRH
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion

namespace Reg.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointRH

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => sigmaKappa (3 / 2) (Nat.lcmUpto m))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ _hRH : RiemannHypothesis,
    ∃ M₀ : ℕ, 3 ≤ M₀ ∧ ∀ m : ℕ, M₀ ≤ m →
      (Real.exp Real.eulerMascheroniConstant * (Nat.lcmUpto m : ℝ) *
        Real.log (Real.log (Nat.lcmUpto m : ℝ))) ^ (3 / 2 : ℝ) /
          (riemannZeta ((3 / 2 : ℝ) : ℂ)).re < R.readout () () m

theorem actual_law : arena.Law actual :=
  @_root_.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointRH.result

theorem source_bridge :
    (type_of% @_root_.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointRH.result) ↔
      arena.Law actual := Iff.rfl

/-- Refuting any alternative for this exact conditional law entails RH. -/
theorem variation_requires_rh :
    (∃ R : Realization signature, ¬ arena.Law R) → RiemannHypothesis := by
  classical
  rintro ⟨R, hR⟩
  by_contra hn
  apply hR
  intro hRH
  exact False.elim (hn hRH)

/- No Contract.Registration is claimed. The exact source law is vacuous for
every realization if RH is false. Whole-family variation for this law would
therefore prove RH, as variation_requires_rh checks. Adding an unconditional
anchor or assuming RH outside the original telescope would change the source
contract. A lawful enrolled-template readout, variation, sensitivity, dependence
and current binding evidence remain unavailable for this faithful source law. -/

end Reg.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointRH
