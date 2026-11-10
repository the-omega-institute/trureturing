import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.FiniteJetAudit

/-! Source-faithful dependent-family audit evidence for finite original jets. -/

set_option autoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.GroupAlgebra
open FiniteJetCoefficients FiniteJetClassification FiniteJetOrbits OddPrimeJetDeformation
open Reg.Support.FiniteJetAudit
open scoped BigOperators
noncomputable section
universe u
namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients
namespace coefficientMap_apply
structure Scope extends Data.{u} where
  A : Fin (n-1) → K
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Scope.{u}
  (fun s => s.K) (fun s => s.K)
def actual : Realization signature.{u} := realize signature
  (fun _ s x => ∑ i, s.A i * (x ^ s.p ^ (i.val+1) - x)) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature
  (fun i s x => actual.readout i s x + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] {K : Type u} [fk : Field K]
    [ft : Fintype K] [ak : Algebra (ZMod p) K]
    (n : ℕ) (A : Fin (n-1) → K) (x : K),
    (coefficientMap (p := p) n A).val x = f.readout () ⟨⟨p,K,n⟩,A⟩ x
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := h (p := 3) (K := ULift.{u} (ZMod 3)) 1 0 0
  simpa [rejected, actual, realize, coefficientMap_apply] using hb
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  obtain ⟨x, hx⟩ := coefficient_values_ne.{u}
  refine ⟨⟨nine,(fun _ => (1 : Nine.{u}))⟩, x, (0 : Nine.{u}), ?_⟩
  simp only [_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients.coefficientMap_apply] at hx
  simpa [actual, realize, nine,
    _root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients.coefficientMap_apply] using hx

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients.coefficientMap_apply.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients.coefficientMap_apply.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients.coefficientMap_apply.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients.coefficientMap_apply.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients.coefficientMap_apply.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients
    definition := none
    coordinates := #[0, 2, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end coefficientMap_apply
namespace coefficientMap_bijective
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature SizedData.{u}
  (fun s => Fin (s.n-1) → s.K) (fun s => Normalized (p := s.p) (K := s.K))
def actual : Realization signature.{u} := realize signature
  (fun _ s A => coefficientMap (p := s.p) s.n A) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] {K : Type u} [fk : Field K]
    [ft : Fintype K] [ak : Algebra (ZMod p) K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Fintype.card K = p ^ n),
    Function.Bijective (f.readout () ⟨⟨p,K,n⟩,hn,hK⟩)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := h (p := 3) (K := Nine.{u}) (n := 2) (by decide) nine_card
  exact tuples_ne (hb.injective (a₁ := 0) (a₂ := 1) rfl)
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨nineSized, 0, 1, ?_⟩
  exact fun h => tuples_ne ((coefficientMap_bijective (by decide) nine_card).injective h)

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients.coefficientMap_bijective.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients.coefficientMap_bijective.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients.coefficientMap_bijective.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients.coefficientMap_bijective.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients.coefficientMap_bijective.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients
    definition := none
    coordinates := #[0, 2, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end coefficientMap_bijective
end Reg.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients
