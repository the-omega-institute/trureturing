import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.IncompleteBetaShape.Mixture
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Analytic.IncompleteBetaShape.Mixture
open _root_.D5.S3.Analytic.IncompleteBeta (coeff)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set

noncomputable section
namespace Reg.D5.S3.Analytic.IncompleteBetaShape.Mixture

namespace Representation
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ q n => convolution q.1 q.2.1 q.2.2 n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ q n => convolution q.1 q.2.1 q.2.2 n + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {p q b : ℝ}, 0 < p → 0 < q → 0 < b → ∀ n : ℕ,
    R.readout () ⟨p, q, b⟩ n = mixtureFactor (p + q) n b *
      ∫ y in (0 : ℝ)..1, (y * (1 - y)) ^ (b - 1) * mixtureDensity p q n y
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h (p := 1) (q := 1) (b := 1) (by norm_num) (by norm_num) (by norm_num) 0
  have H' := convolution_eq_mixtureMean (p := 1) (q := 1) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) 0
  change convolution 1 1 1 0 + 1 = _ at H
  linarith
def family : Registration arena (type_of% @convolution_eq_mixtureMean) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@convolution_eq_mixtureMean, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨1, 1, 1⟩, 0, 1, ?_⟩
    change convolution 1 1 1 0 ≠ convolution 1 1 1 1
    delta convolution coeff
    norm_num [Finset.sum_range_succ, Real.Gamma_add_one]
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@convolution_eq_mixtureMean) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Mixture.Representation.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Mixture.Representation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ q n => convolution q.1 q.2.1 q.2.2 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBeta.Moment
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Representation

end Reg.D5.S3.Analytic.IncompleteBetaShape.Mixture
