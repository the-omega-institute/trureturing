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
    owner := `D5.S3.Analytic.IncompleteBetaShape.Mixture
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


namespace KernelMean
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
      _root_.D5.S3.Analytic.IncompleteBeta.Comparison.betaMean
        (_root_.D5.S3.Analytic.IncompleteBetaShape.Kernel.H (p + q) n b)
        ((p + q) / 2) ((p - q) / 2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h (p := 1) (q := 1) (b := 1) (by norm_num) (by norm_num) (by norm_num) 0
  have H' := convolution_eq_betaMean_H (p := 1) (q := 1) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) 0
  change convolution 1 1 1 0 + 1 = _ at H
  linarith
def family : Registration arena (type_of% @convolution_eq_betaMean_H) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@convolution_eq_betaMean_H, rejected, rejected_law⟩
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
    (@convolution_eq_betaMean_H) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Mixture.KernelMean.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Mixture.KernelMean.family
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
    owner := `D5.S3.Analytic.IncompleteBetaShape.Mixture
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
end KernelMean

namespace Affine
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℝ, ℕ) (fun _ => ℝ → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ q g => ∫ y in (0 : ℝ)..1,
    mixtureDensity q.1 q.2.1 q.2.2 y * g y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ q g => (∫ y in (0 : ℝ)..1,
    mixtureDensity q.1 q.2.1 q.2.2 y * g y) + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {p q : ℝ}, 0 < p → 0 < q → ∀ (n : ℕ) (g : ℝ → ℝ), Measurable g →
    IntervalIntegrable (fun y => mixtureDensity p q n y * g y)
      MeasureTheory.volume 0 1 →
    R.readout () ⟨p, q, n⟩ g =
      (Real.Gamma p * Real.Gamma q * Real.Gamma ((n : ℝ) + 2) /
        Real.Gamma (p + q + n + 2))⁻¹ *
        ∫ v in (0 : ℝ)..1, v ^ (p - 1) * (1 - v) ^ (q - 1) *
          ∫ s in (0 : ℝ)..1, s ^ (p + q - 1) * (1 - s) ^ ((n : ℝ) + 1) *
            ∫ u in (0 : ℝ)..1, g (s * v + (1 - s) * u)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h (p := 1) (q := 1) (by norm_num) (by norm_num) 0 (fun _ => 0)
    measurable_const (by simpa using (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume 0 1))
  change (∫ y in (0 : ℝ)..1, mixtureDensity 1 1 0 y * 0) + 1 = _ at H
  simp at H
private theorem density_one : (∫ y in (0 : ℝ)..1, mixtureDensity 1 1 0 y) = 1 := by
  have h := convolution_eq_mixtureMean (p := 1) (q := 1) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) 0
  norm_num [convolution, coeff, mixtureFactor, Real.Gamma_add_one] at h
  linarith
def family : Registration arena (type_of% @mixture_eq_affine) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mixture_eq_affine, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨1, 1, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    change (∫ y in (0 : ℝ)..1, mixtureDensity 1 1 0 y * 0) ≠
      (∫ y in (0 : ℝ)..1, mixtureDensity 1 1 0 y * 1)
    simpa [density_one]
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mixture_eq_affine) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Mixture.Affine.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBetaShape.Mixture.Affine.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q g => ∫ y in (0 : ℝ)..1,
    mixtureDensity q.1 q.2.1 q.2.2 y * g y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBetaShape.Mixture
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Affine

end Reg.D5.S3.Analytic.IncompleteBetaShape.Mixture
