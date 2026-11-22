import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PetzDyadicStripEnergy
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the dyadic strip energy identities and bound. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.PetzDyadicStripEnergy
open _root_.PetzStripGramRemainder (remainder stripGram)
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)
open scoped BigOperators

namespace Reg.D5.S3.Analytic.PetzDyadicStripEnergy

universe u

private abbrev scalarSignature : Signature := signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ _ => False) (fun e => nomatch e)

namespace Remainder

def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ x y : ℝ,
    R.readout () () (remainder x y) (2 * stripGram (x / 2) (y / 2))

private theorem rejectedLaw : ¬ arena.Law rejected := fun law => law 0 0

def family : Registration arena (type_of% @remainder_eq_two_mul_stripGram_half) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@remainder_eq_two_mul_stripGram_half, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    cases role
    refine ⟨(), 0, 1, ?_⟩
    intro equal
    have h := congrFun equal 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@remainder_eq_two_mul_stripGram_half) (Realization scalarSignature) Unit Unit where
  unitName := `PetzDyadicStripEnergy.remainder_eq_two_mul_stripGram_half.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicStripEnergy.Remainder.family
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
    owner := `D5.S3.Analytic.PetzDyadicStripEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Remainder

namespace Decomposition

def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {ι : Type u} [Fintype ι] (x : ι → ℝ) (c : ι → ℂ) (M : ℕ),
    R.readout () () (stripEnergy x c)
      ((∑ m ∈ Finset.range M, (2 : ℝ) ^ m * logisticEnergy (fun i => x i / 2 ^ m) c) +
        (2 : ℝ) ^ M * stripEnergy (fun i => x i / 2 ^ M) c)

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro law
  exact law (ι := ULift.{u} Unit) (fun _ => 0) (fun _ => 0) 0

def family : Registration arena.{u} (type_of% @stripEnergy_dyadic.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@stripEnergy_dyadic.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    cases role
    refine ⟨(), 0, 1, ?_⟩
    intro equal
    have h := congrFun equal 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stripEnergy_dyadic.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `PetzDyadicStripEnergy.stripEnergy_dyadic.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicStripEnergy.Decomposition.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicStripEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Decomposition

namespace LowerBound

def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {ι : Type u} [Fintype ι] (x : ι → ℝ) (c : ι → ℂ) (M : ℕ),
    0 ≤ ∑ m ∈ Finset.range M, (2 : ℝ) ^ m * logisticEnergy (fun i => x i / 2 ^ m) c ∧
      R.readout () () (∑ m ∈ Finset.range M, (2 : ℝ) ^ m * logisticEnergy (fun i => x i / 2 ^ m) c)
        (stripEnergy x c)

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro law
  exact (law (ι := ULift.{u} Unit) (fun _ => 0) (fun _ => 0) 0).2

def family : Registration arena.{u} (type_of% @stripEnergy_dyadic_lower_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@stripEnergy_dyadic_lower_bound.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    cases role
    refine ⟨(), 0, 1, ?_⟩
    intro equal
    have h := congrFun equal 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stripEnergy_dyadic_lower_bound.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `PetzDyadicStripEnergy.stripEnergy_dyadic_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicStripEnergy.LowerBound.family
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
    owner := `D5.S3.Analytic.PetzDyadicStripEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LowerBound

#print axioms Remainder.audit
#print axioms Decomposition.audit
#print axioms LowerBound.audit

end Reg.D5.S3.Analytic.PetzDyadicStripEnergy
