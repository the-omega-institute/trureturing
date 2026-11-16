import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.PolynomialCanonicalRecordCriterion
import Reg.Support.SingleDependentReadout

/-! Full-source reconstruction for the polynomial record criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect (strictInteger)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff (firstLayerPrice)
open _root_.D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)

namespace Reg.D5.S3.Arith.Robin.PriceRecord.PolynomialCanonicalRecordCriterion

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ r k =>
    robinLogMargin (strictInteger (firstLayerPrice (((k ^ r : ℕ) : ℝ) + 1))))
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ r : ℕ, 2 ≤ r → ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 / 2 →
    ((∃ M : ℝ, 0 ≤ M ∧ ∃ k0 : ℕ, 2 ≤ k0 ∧ ∀ k : ℕ, k0 ≤ k →
      -M ≤ Real.rpow (((k ^ r : ℕ) : ℝ)) alpha *
        Real.log (((k ^ r : ℕ) : ℝ)) * V.readout () r k) ↔
    (∀ rho : ℂ, _root_.D5.S3.Weil.ZeroSum.IsNontrivialZero rho →
      rho.re ≤ 1 - alpha))

private theorem actual_law : arena.Law actual :=
  by simpa only [arena, actual, realize] using
    @_root_.D5.S3.Arith.Robin.PriceRecord.PolynomialCanonicalRecordCriterion.result

private theorem source_reconstruction :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.PolynomialCanonicalRecordCriterion.result)) ↔
      arena.Law actual := Iff.rfl

/- The law uses all natural r and k and all real alpha, M, with the original
   strict all-layer integer and actual zero predicate. A complete
   DependentFamily.Registration additionally requires whole-family variation,
   sensitivity and actual observational dependence, followed by lawful source
   selection and a Contract.Registration using the enrolled realize template.
   These obligations are not supplied by this reconstruction. No validated
   four-slot registration or mathematical impossibility of one is asserted. -/

end Reg.D5.S3.Arith.Robin.PriceRecord.PolynomialCanonicalRecordCriterion
