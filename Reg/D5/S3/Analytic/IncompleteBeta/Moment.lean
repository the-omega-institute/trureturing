import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.IncompleteBeta.Moment
import Reg.Support.SingleDependentReadout

/-! Dependent-family evidence for the beta moment kernel. -/

open _root_.D5.S3.Analytic.IncompleteBeta
open _root_.D5.S3.Analytic.IncompleteBeta.Moment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set

noncomputable section
namespace Reg.D5.S3.Analytic.IncompleteBeta.Moment

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, ℕ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ q u => W q.1 q.2 u) (fun e => nomatch e)
def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def stepReadout : Realization signature :=
  realize signature (fun _ _ u => if u = 1/2 then 0 else 1) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0⟩, 0, 1/2, ?_⟩
  exact ne_of_lt (W_strictMonoOn (a := 1) (by norm_num) 0
    (by norm_num) (by norm_num) (by norm_num))

namespace Monotonicity
def arena : Arena where
  signature := signature
  Law R := ∀ {a : ℝ}, 0 < a → ∀ n : ℕ,
    StrictMonoOn (R.readout () ⟨a, n⟩) (Icc 0 (1/2))
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have H := h (a := 1) (by norm_num) 0 (by norm_num) (by norm_num) (by norm_num : (0:ℝ)<1/2)
  exact (lt_irrefl (0:ℝ)) H
def family : Registration arena (type_of% @W_strictMonoOn) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@W_strictMonoOn, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@W_strictMonoOn) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBeta.Moment.Monotonicity.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBeta.Moment.Monotonicity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q u => W q.1 q.2 u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBeta.Moment
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Monotonicity

namespace Symmetry
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℕ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ q u => W q.2 q.1 u) (fun e => nomatch e)
def identityReadout : Realization signature :=
  realize signature (fun _ _ u => u) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (u : ℝ) {a : ℝ},
    R.readout () ⟨n, a⟩ (1-u) = R.readout () ⟨n, a⟩ u
private theorem rejected_law : ¬ arena.Law identityReadout := by
  intro h
  have H := h 0 0 (a := 1)
  norm_num [identityReadout, realize] at H
def family : Registration arena (type_of% @W_symm) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@W_symm, identityReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual identityReadout rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨0, 1⟩, 0, 1/2, ?_⟩
    exact ne_of_lt (W_strictMonoOn (a := 1) (by norm_num) 0
      (by norm_num) (by norm_num) (by norm_num))
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@W_symm) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBeta.Moment.Symmetry.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBeta.Moment.Symmetry.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q u => W q.2 q.1 u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBeta.Moment
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Symmetry

namespace Continuity
def arena : Arena where
  signature := signature
  Law R := ∀ {a : ℝ}, 0 < a → ∀ n : ℕ,
    ContinuousOn (R.readout () ⟨a, n⟩) (Icc 0 1)
private theorem rejected_law : ¬ arena.Law stepReadout := by
  intro h
  have hc := h (a := 1) (by norm_num) 0
  have hct : ContinuousAt (fun x : ℝ => if x = 1/2 then (0:ℝ) else 1) (1/2) :=
    hc.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨d, hd, hbound⟩ := Metric.continuousAt_iff.mp hct (1/2) (by norm_num)
  let y := (1/2:ℝ) + d/2
  have hy : y ≠ 1/2 := by dsimp [y]; linarith
  have hdist : dist y (1/2:ℝ) < d := by
    rw [Real.dist_eq, abs_of_pos]; all_goals dsimp [y]; linarith
  have he := hbound hdist
  norm_num [hy] at he
def family : Registration arena (type_of% @W_continuousOn) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@W_continuousOn, stepReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual stepReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@W_continuousOn) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBeta.Moment.Continuity.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBeta.Moment.Continuity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q u => W q.1 q.2 u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBeta.Moment
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Continuity

namespace Derivative
def arena : Arena where
  signature := signature
  Law R := ∀ {a u : ℝ}, 0 < a → ∀ n : ℕ, u ∈ Ioo 0 1 →
    HasDerivAt (R.readout () ⟨a, n⟩)
      (u^(a-1)*(1-u)^(a+n) / (Real.Gamma a*Real.Gamma (a+n+1)) -
        u^(a+n)*(1-u)^(a-1) / (Real.Gamma (a+n+1)*Real.Gamma a)) u
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have H := h (a := 1) (u := 1/4) (by norm_num) 0 (by norm_num)
  have he := H.unique (hasDerivAt_const (1/4:ℝ) (0:ℝ))
  norm_num [Real.Gamma_add_one] at he
def family : Registration arena (type_of% @W_hasDerivAt) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@W_hasDerivAt, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@W_hasDerivAt) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBeta.Moment.Derivative.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBeta.Moment.Derivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q u => W q.1 q.2 u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBeta.Moment
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Derivative

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
  Law R := ∀ {a s t : ℝ}, 0 < a → 0 < s → 0 < t → ∀ n : ℕ,
    R.readout () ⟨a, s, t⟩ n =
      Real.Gamma (2*a+s+t+n) / (Real.Gamma s * Real.Gamma t) *
        ∫ u in (0:ℝ)..1, u^(s-1)*(1-u)^(t-1)*W a n u
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h (a := 1) (s := 1) (t := 1) (by norm_num) (by norm_num) (by norm_num) 0
  have H' := convolution_eq_betaMean (a := 1) (s := 1) (t := 1)
    (by norm_num) (by norm_num) (by norm_num) 0
  change convolution 1 1 1 0 + 1 = _ at H
  linarith
def family : Registration arena (type_of% @convolution_eq_betaMean) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@convolution_eq_betaMean, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨1, 1, 1⟩, 0, 1, ?_⟩
    change convolution 1 1 1 0 ≠ convolution 1 1 1 1
    norm_num [convolution, coeff, Finset.sum_range_succ, Real.Gamma_add_one]
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@convolution_eq_betaMean) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBeta.Moment.Representation.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBeta.Moment.Representation.family
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

end Reg.D5.S3.Analytic.IncompleteBeta.Moment
