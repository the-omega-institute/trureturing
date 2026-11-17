import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.Cyclic.VerifiedPrimeFactorStrippingCost
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift

/-! Source-bound complete telescope for exact stripping cost. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.FiniteGroups.Cyclic.VerifiedPrimeFactorStrippingCost
universe u

abbrev SourceData :=
  Σ G : Type u, Σ _ : Monoid G, Σ _ : DecidableEq G, Σ _ : G, List ℕ

abbrev signature : Signature where
  Params := SourceData.{u}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ × ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p m => by
    letI := p.2.1
    letI := p.2.2.1
    exact PrimeFactorStrippingCost.stripFactorsCost p.2.2.2.1 p.2.2.2.2 m) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => (0, 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {G : Type u} [hG : Monoid G] [hD : DecidableEq G]
    (x : G) (P : List ℕ) (m : ℕ),
    let M := R.readout () ⟨G, hG, hD, x, P⟩ m
    M.1 = PrimeFactorStripping.stripFactors x P m ∧
      M.2 ≤ P.length + Nat.log 2 m

abbrev statement : Prop := type_of% @PrimeFactorStrippingCost.stripFactorsCost_spec.{u}

theorem bridge : statement.{u} ↔ arena.{u}.Law actual.{u} := Iff.rfl

def testData : SourceData.{u} :=
  ⟨ULift.{u} ℕ, inferInstance, inferInstance, 1, []⟩

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := h (G := ULift.{u} ℕ) 1 [] 1
  change (0, 0).1 = PrimeFactorStripping.stripFactors (1 : ULift.{u} ℕ) [] 1 ∧
    (0, 0).2 ≤ [].length + Nat.log 2 1 at hh
  norm_num [PrimeFactorStripping.stripFactors] at hh

theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro ⟨⟩
  refine ⟨testData.{u}, 1, 2, ?_⟩
  change (1, 0) ≠ (2, 0)
  decide

def family : Registration arena.{u} statement.{u} where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @PrimeFactorStrippingCost.stripFactorsCost_spec, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro ⟨⟩
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def entry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PrimeFactorStrippingCost.stripFactorsCost_spec.{u})
    (type_of% (realize signature.{u} (fun _ p m => by
      letI := p.2.1
      letI := p.2.2.1
      exact PrimeFactorStrippingCost.stripFactorsCost p.2.2.2.1 p.2.2.2.2 m) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.Cyclic.VerifiedPrimeFactorStrippingCost.informationUnit
  realizationName := `Reg.D5.S3.FiniteGroups.Cyclic.VerifiedPrimeFactorStrippingCost.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p m => by
    letI := p.2.1
    letI := p.2.2.1
    exact PrimeFactorStrippingCost.stripFactorsCost p.2.2.2.1 p.2.2.2.2 m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.Cyclic.VerifiedPrimeFactorStrippingCost
    definition := none
    coordinates := #[0, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.Cyclic.VerifiedPrimeFactorStrippingCost
