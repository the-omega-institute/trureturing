import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PetzStripGramRemainder
import Reg.Support.SingleDependentReadout

/-! Source-bound readouts for the exact strip Gram and its logistic remainder. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.PetzStripGramRemainder
open PetzLogisticMidline (lowerWeight upperWeight)
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)
open scoped BigOperators

namespace Reg.D5.S3.Analytic.PetzStripGramRemainder

namespace Gram

private abbrev scalarSignature : Signature := signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ x y : ℝ, Integrable (weightedPair lowerWeight 0 x y) ∧
    Integrable (weightedPair upperWeight (1 / 2) x y) ∧
    R.readout () () ((∫ t, weightedPair lowerWeight 0 x y t) +
      ∫ t, weightedPair upperWeight (1 / 2) x y t) (stripGram x y : ℂ)

private theorem rejectedLaw : ¬ arena.Law rejected := fun law => (law 0 0).2.2

def family : Registration arena (type_of% @weighted_strip_gram) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weighted_strip_gram, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    cases role
    refine ⟨(), 0, 1, ?_⟩
    intro equal
    have h := congrFun equal 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_strip_gram) (Realization scalarSignature) Unit Unit where
  unitName := `PetzStripGramRemainder.weighted_strip_gram.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzStripGramRemainder.Gram.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzStripGramRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Gram

namespace Remainder

universe u

private abbrev scalarSignature : Signature := signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {ι : Type u} [Fintype ι] (x : ι → ℝ) (c : ι → ℂ),
    R.readout () () 0 (∑ i, ∑ j, (star (c i) * c j) * (remainder (x i) (x j) : ℂ)).re

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro law
  exact law (ι := ULift.{u} Unit) (fun _ => 0) (fun _ => 0)

def family : Registration arena.{u} (type_of% @remainder_quadratic_nonneg.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@remainder_quadratic_nonneg.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    cases role
    refine ⟨(), 0, 1, ?_⟩
    intro equal
    have h := congrFun equal 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@remainder_quadratic_nonneg.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `PetzStripGramRemainder.remainder_quadratic_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzStripGramRemainder.Remainder.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzStripGramRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Remainder

end Reg.D5.S3.Analytic.PetzStripGramRemainder
