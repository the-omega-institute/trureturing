import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.LegendrePrimitiveGap
import Reg.Support.SingleDependentReadout

noncomputable section

open _root_.D5.S3.Analytic.PolynomialL2Derivative
open _root_.D5.S3.Analytic.LegendrePrimitiveGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial MeasureTheory Set
open scoped Interval ComplexConjugate

namespace Reg.D5.S3.Analytic.LegendrePrimitiveGap

namespace Mixed
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _d : ℕ, ℕ → ℂ) (fun _ => ℕ → ℂ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ p b => moment (expansion p.1 p.2) ((expansion p.1 b).map (starRingEnd ℂ))) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (a b : ℕ → ℂ),
    R.readout () ⟨d, a⟩ b =
      ∑ n ∈ Finset.range d, a n * conj (b n) / (2 * (n : ℂ) + 1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 0 (fun _ => 0) (fun _ => 0)
  norm_num [rejected, realize] at hf
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, (fun _ => 1)⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, moment, expansion, legendreC, Polynomial.shiftedLegendre]
def family : Registration arena (type_of% (@mixed_expansion)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mixed_expansion, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mixed_expansion) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.LegendrePrimitiveGap.mixed_expansion.audit
  realizationName := `Reg.D5.S3.Analytic.LegendrePrimitiveGap.Mixed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p b => moment (expansion p.1 p.2) ((expansion p.1 b).map (starRingEnd ℂ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.LegendrePrimitiveGap
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Mixed

namespace Primitive
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete finite telescope, with arbitrary complex coefficients and
the empty expansion. The family varies the primitive's native norm operation. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (d q : ℕ) (hq : 1 ≤ q) (a : ℕ → ℂ)
    (ha : ∀ n < q, a n = 0),
    (∫ x in Icc (0 : ℝ) 1,
      (R.readout () () (∫ t in (0 : ℝ)..x, (expansion d a).eval (t : ℂ))) ^ 2) ≤
      (1 / (4 * (q : ℝ) * ((q : ℝ) + 1))) *
        (∫ x in Icc (0 : ℝ) 1, ‖(expansion d a).eval (x : ℂ)‖ ^ 2)


/-- At d=0,q=1,a=0 the constant-one observation demands 1≤0. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 0 1 (by norm_num) (fun _ => 0) (by intro n hn; rfl)
  norm_num [rejected, realize, expansion, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hf

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
  norm_num

def family : Registration arena (type_of% @complex_legendre_primitive_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@complex_legendre_primitive_gap, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

/-- The primitive energy occurrence selects the native norm function. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complex_legendre_primitive_gap) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.LegendrePrimitiveGap.complex_legendre_primitive_gap.audit
  realizationName := `Reg.D5.S3.Analytic.LegendrePrimitiveGap.Primitive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.LegendrePrimitiveGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Primitive

end Reg.D5.S3.Analytic.LegendrePrimitiveGap
