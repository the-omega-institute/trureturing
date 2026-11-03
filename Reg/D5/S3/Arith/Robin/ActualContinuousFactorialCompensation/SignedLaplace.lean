import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SignedLaplace
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open _root_.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SignedLaplace

/- The source-law attempt retains the complete actual G pullback and both
conjuncts of the theorem. The domain is the full real line, not a finite audit
catalogue. Whole-family intervention, variation/sensitivity, observational
dependence and a lawful source selection are still missing. Consequently this
is neither a Contract.Registration nor a declared_validated registration. -/

/- The source law reuses Basic.G_formula and the arbitrary-rate
PrimorialFirstOrderConcentrationCounterexample.exp_moment_integrable supplier;
the mirror retains the exact existing law and source bridge. -/

namespace G_signed_laplace_negative

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => G (Real.exp t)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V :=
    IntegrableOn (fun t : ℝ => (1 - 10 * t) * Real.exp (-(21 / 2 : ℝ) * t) *
      (V.readout () ()) t) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), (1 - 10 * t) * Real.exp (-(21 / 2 : ℝ) * t) *
      (V.readout () ()) t) < -(1 / 1000 : ℝ)

private theorem actual_law : arena.Law actual := G_signed_laplace_negative

private theorem sourceBridge :
    (type_of% (@G_signed_laplace_negative)) ↔ arena.Law actual := Iff.rfl

end G_signed_laplace_negative

end Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SignedLaplace
