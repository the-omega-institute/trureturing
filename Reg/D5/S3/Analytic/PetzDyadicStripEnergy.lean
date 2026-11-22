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
open scoped BigOperators Matrix ComplexOrder
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open _root_.D5.S3.Quantum.Recovery.BKMFlagRefinement (relativeEntropyOfMatrices)

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

namespace PhysicalIdentity

private def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := scalarSignature
  Law F := ∀ {r : Type u} {e : Type u} [Fintype r] [DecidableEq r]
    [Fintype e] [DecidableEq e] [Nonempty e]
    {A B : Matrix (r × e) (r × e) ℂ} (hA : A.PosDef) (hB : B.PosDef),
    F.readout () ()
      (relativeEntropyOfMatrices A B -
        relativeEntropyOfMatrices (partialTraceRight A) (partialTraceRight B))
      (∑ ab, stripEnergy (physicalFrequency hA hB ab) (physicalCoefficient hA hB ab))

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (r := ULift.{u} Unit) (e := ULift.{u} Unit)
    Matrix.PosDef.one Matrix.PosDef.one

def family : Registration arena.{u} (type_of% @umegakiLoss_eq_stripEnergy.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@umegakiLoss_eq_stripEnergy.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    cases role
    refine ⟨(), 0, 1, ?_⟩
    intro equal
    have h := congrFun equal 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@umegakiLoss_eq_stripEnergy.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `PetzDyadicStripEnergy.umegakiLoss_eq_stripEnergy.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicStripEnergy.PhysicalIdentity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
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
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PhysicalIdentity

namespace PhysicalDyadic

private def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := scalarSignature
  Law F := ∀ {r : Type u} {e : Type u} [Fintype r] [DecidableEq r]
    [Fintype e] [DecidableEq e] [Nonempty e]
    {A B : Matrix (r × e) (r × e) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (M : ℕ),
    let loss := relativeEntropyOfMatrices A B -
      relativeEntropyOfMatrices (partialTraceRight A) (partialTraceRight B)
    let partialEnergy := ∑ ab, ∑ m ∈ Finset.range M, (2 : ℝ) ^ m *
      logisticEnergy (fun k => physicalFrequency hA hB ab k / 2 ^ m)
        (physicalCoefficient hA hB ab)
    let tail := ∑ ab, (2 : ℝ) ^ M *
      stripEnergy (fun k => physicalFrequency hA hB ab k / 2 ^ M)
        (physicalCoefficient hA hB ab)
    F.readout () () loss (partialEnergy + tail) ∧ 0 ≤ partialEnergy ∧ partialEnergy ≤ loss

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h (r := ULift.{u} Unit) (e := ULift.{u} Unit)
    Matrix.PosDef.one Matrix.PosDef.one 0).1

def family : Registration arena.{u} (type_of% @umegakiLoss_dyadic.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@umegakiLoss_dyadic.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    cases role
    refine ⟨(), 0, 1, ?_⟩
    intro equal
    have h := congrFun equal 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@umegakiLoss_dyadic.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `PetzDyadicStripEnergy.umegakiLoss_dyadic.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicStripEnergy.PhysicalDyadic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
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
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PhysicalDyadic

#print axioms Remainder.audit
#print axioms Decomposition.audit
#print axioms LowerBound.audit
#print axioms PhysicalIdentity.audit
#print axioms PhysicalDyadic.audit

end Reg.D5.S3.Analytic.PetzDyadicStripEnergy
