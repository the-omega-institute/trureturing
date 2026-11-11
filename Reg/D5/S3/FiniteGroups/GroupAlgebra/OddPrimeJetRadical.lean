import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadical
import Reg.Support.OddPrimeJetAudit

/-! Full-telescope source evidence for the commutant's constant-line action. -/

set_option autoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.GroupAlgebra
open OddPrimeJetDeformation OddPrimeJetRadical

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadical
universe u
namespace constant_action

abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature
  Reg.Support.OddPrimeJetAudit.Data.{u}
  (fun d => d.K) (fun d => Reg.Support.OddPrimeJetAudit.Vector d)

def actual : Realization signature.{u} := realize signature
  (fun _ d z => by
    letI := d.prime
    letI := d.odd
    letI := d.field
    letI := d.algebra
    exact constantLinear z) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun _ d z => by
    letI := d.prime
    letI := d.odd
    letI := d.field
    letI := d.algebra
    exact constantLinear (z + 1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type u} [kk : Field K] [ka : Algebra (ZMod p) K]
    (q : K →ₗ[ZMod p] K) (hq : q 1 = 0)
    (X : commutantAlgebra (p := p) (K := K) q) (z : K),
    X.val (r.readout () ⟨p, pp, po, K, kk, ka⟩ z) =
      constantLinear (p := p) (K := K) (leadingScalar q X * z)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hbad
  let d : Reg.Support.OddPrimeJetAudit.Data.{u} := Reg.Support.OddPrimeJetAudit.testData
  letI := d.prime
  letI := d.odd
  letI := d.field
  letI := d.algebra
  have h := hbad (p := d.p) (K := d.K) 0 rfl 1 0
  have hz : constantLinear (p := d.p) (K := d.K) 1 = 0 := by
    simpa [rejected, realize, constantLinear] using h
  exact Reg.Support.OddPrimeJetAudit.vectorOne_ne_zero d hz

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let d : Reg.Support.OddPrimeJetAudit.Data.{u} := Reg.Support.OddPrimeJetAudit.testData
  letI := d.field
  refine ⟨d, 0, 1, ?_⟩
  intro h
  apply Reg.Support.OddPrimeJetAudit.vectorOne_ne_zero d
  simpa [actual, realize, Reg.Support.OddPrimeJetAudit.vectorOne, constantLinear] using h.symm

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadical.constant_action.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadical.constant_action.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadical.constant_action.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadical.constant_action.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadical.constant_action.family
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
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadical
    definition := none
    coordinates := #[0,1,2,3,4,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","arg","arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end constant_action
end Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadical
