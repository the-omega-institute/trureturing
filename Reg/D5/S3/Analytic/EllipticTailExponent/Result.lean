import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.EllipticTailExponent.Result
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.EllipticTailExponent.Result
open _root_.D5.S3.Analytic.EllipticTailExponent.Defs
open _root_.D5.S3.Analytic.EllipticTailExponent.Bounds
open _root_.D5.S3.Analytic.EllipticTailExponent.Result
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter
open scoped BigOperators Topology
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ n a => lambda10 n a) (fun e => nomatch e)
def sActual : Realization signature := realize signature (fun _ n a => S n a) (fun e => nomatch e)
def zeroReadout : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def twoReadout : Realization signature := realize signature (fun _ _ _ => 2) (fun e => nomatch e)
def shiftedReadout : Realization signature := realize signature (fun _ n a => lambda10 n a + 1) (fun e => nomatch e)
def sineReadout : Realization signature := realize signature
  (fun _ _ a => Real.sin (Real.pi * a) / (Real.pi * (1 - a))) (fun e => nomatch e)

private theorem lambdaDependence : ObservationalDependence signature actual := by
  intro i
  by_contra! h
  have he : lambda10 0 = fun _ => 0 := by
    funext a
    have hh := h 0 a 0
    simpa [actual, realize, lambda10] using hh
  have ht := tendsto_lambda10 0
  rw [he] at ht
  have hz := tendsto_nhds_unique ht (tendsto_const_nhds (x := (0 : ℝ)))
  norm_num at hz

private theorem sDependence : ObservationalDependence signature sActual := by
  intro i
  refine ⟨0, 0, 1 / 2, ?_⟩
  norm_num [sActual, realize, S, g6]

namespace Denominator

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) {a : ℝ}, 0 < a → a ≤ 1 / 2 →
    0 < Real.sin (Real.pi * a) - Real.pi * (1 - a) * R.readout () n a

private theorem rejected_law : ¬ arena.Law sineReadout := by
  intro h
  have hh := @h 0 (1 / 2) (by norm_num) (by norm_num)
  change 0 < Real.sin (Real.pi * (1 / 2)) - Real.pi * (1 - 1 / 2) *
    (Real.sin (Real.pi * (1 / 2)) / (Real.pi * (1 - 1 / 2))) at hh
  have hp : Real.pi * (1 - (1 / 2 : ℝ)) ≠ 0 := by positivity
  have he : Real.sin (Real.pi * (1 / 2)) - Real.pi * (1 - 1 / 2) *
      (Real.sin (Real.pi * (1 / 2)) / (Real.pi * (1 - 1 / 2))) = 0 := by field_simp; ring
  rw [he] at hh
  exact lt_irrefl 0 hh

def family : Registration arena (type_of% @denominator_pos) where
  actual := sActual
  bridge := Iff.rfl
  variation := ⟨@denominator_pos, sineReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law sActual sineReadout rejected_law
  dependence := sDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@denominator_pos) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.EllipticTailExponent.Result.Denominator.unit
  realizationName := `Reg.D5.S3.Analytic.EllipticTailExponent.Result.Denominator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n a => S n a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.EllipticTailExponent.Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Denominator

namespace Identity

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) {a : ℝ}, 0 < a → a ≤ 1 / 2 →
    R.readout () n a = 2 + a * deriv (U n) a / U n a

private theorem rejected_law : ¬ arena.Law shiftedReadout := by
  intro h
  have hh := @h 0 (1 / 2) (by norm_num) (by norm_num)
  have he := lambda10_eq 0 (a := 1 / 2) (by norm_num) (by norm_num)
  change lambda10 0 (1 / 2) + 1 = _ at hh
  linarith

def family : Registration arena (type_of% @lambda10_eq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lambda10_eq, shiftedReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shiftedReadout rejected_law
  dependence := lambdaDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lambda10_eq) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.EllipticTailExponent.Result.Identity.unit
  realizationName := `Reg.D5.S3.Analytic.EllipticTailExponent.Result.Identity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n a => lambda10 n a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.EllipticTailExponent.Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Identity

namespace Upper

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) {a : ℝ}, 0 < a → a ≤ 1 / 2 → R.readout () n a < 2

private theorem rejected_law : ¬ arena.Law twoReadout := by
  intro h
  exact lt_irrefl 2 (@h 0 (1 / 2) (by norm_num) (by norm_num))

def family : Registration arena (type_of% @lambda10_lt_two) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lambda10_lt_two, twoReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual twoReadout rejected_law
  dependence := lambdaDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lambda10_lt_two) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.EllipticTailExponent.Result.Upper.unit
  realizationName := `Reg.D5.S3.Analytic.EllipticTailExponent.Result.Upper.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n a => lambda10 n a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.EllipticTailExponent.Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Upper

namespace Limit

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, Tendsto (fun a => R.readout () n a) (𝓝[>] 0) (𝓝 2)

private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have hh := h 0
  have he := tendsto_nhds_unique hh (tendsto_const_nhds (x := (0 : ℝ)))
  norm_num at he

def family : Registration arena (type_of% @tendsto_lambda10) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tendsto_lambda10, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroReadout rejected_law
  dependence := lambdaDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tendsto_lambda10) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.EllipticTailExponent.Result.Limit.unit
  realizationName := `Reg.D5.S3.Analytic.EllipticTailExponent.Result.Limit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n a => lambda10 n a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.EllipticTailExponent.Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Limit


end
end Reg.D5.S3.Analytic.EllipticTailExponent.Result
