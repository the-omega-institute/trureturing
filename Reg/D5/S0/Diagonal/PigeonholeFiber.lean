import D5.S0.Diagonal.PigeonholeFiber
import LeanInformationAuditInterface.Contract.AuricFib

namespace Reg.D5.S0.Diagonal.PigeonholeFiber
open _root_.D5.S0.Diagonal.PigeonholeFiber
open _root_.D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit.Analysis
open LeanInformationAudit.AuricFib.Contract (Application)
universe u

/-- Objects, readings and the actual map vary together; states and outputs retain
both dependencies. The cardinality premise remains in the full source law. -/
abbrev Parameters := (Objects : Type u) × (Readings : Type u) × (Objects → Readings)

abbrev signature : DependentFamily.Signature where
  Params := Parameters.{u}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u} where
  readout _ p := p.2.2
  anchor e := nomatch e

def fullLaw (r : DependentFamily.Realization signature.{u}) : Prop :=
  ∀ {Objects Readings : Type u} (read : Objects → Readings)
    (_hcard : Cardinal.mk Readings < Cardinal.mk Objects),
    ∃ x y, x ≠ y ∧ r.readout () ⟨Objects, Readings, read⟩ x =
      r.readout () ⟨Objects, Readings, read⟩ y

abbrev source : Source (@finite_reading_has_fiber.{u}) where
  signature := signature
  actual := actual
  rebuild := fullLaw
  reconstruction := .exact
  selection := {
    owner := `D5.S0.Diagonal.PigeonholeFiber
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }

/-- The total task is the theorem's actual reading. Every repeated layer is kept. -/
def plan : Plan source.{u} where
  task := ()
  initial := [()]
  additions := [[], [()]]

def threeReading (x : Fin 3) : Bool := x == 1

abbrev threeDomain : Domain source.{0} :=
  Domain.fiber source ⟨Fin 3, Bool, threeReading⟩

abbrev threePresentation : FinitePresentation plan threeDomain where
  stateFintype := inferInstanceAs (Fintype (Fin 3))
  stateDecidableEq := inferInstanceAs (DecidableEq (Fin 3))
  enumeration := { states := [0, 1, 2], nodup := by decide, complete := by decide }
  values _ := ![.bool false, .bool true, .bool false]
  decode _ := fun v => match v with | .bool b => some b | _ => none
  values_correct := by decide
  kernel _ := ![![true, false, true], ![false, true, false], ![true, false, true]]
  kernel_correct := by decide
  taskValues := ![.bool false, .bool true, .bool false]
  task_correct := by decide
  layers _ := ![![true, false, true], ![false, true, false], ![true, false, true]]
  layers_correct := by decide

/-- A three-object, two-reading source; no Fibonacci semantics are supplied. -/
def finiteAnalysis : Application (@finite_reading_has_fiber.{0}) where
  evidence := .typed {
    source := source
    plan := plan
    acquisition := .finite threeDomain threePresentation }

abbrev constantDomain : Domain source.{0} :=
  Domain.fiber source ⟨Bool, Unit, fun _ => ()⟩

abbrev constantPresentation : FinitePresentation plan constantDomain where
  stateFintype := inferInstanceAs (Fintype Bool)
  stateDecidableEq := inferInstanceAs (DecidableEq Bool)
  enumeration := { states := [false, true], nodup := by decide, complete := by decide }
  values _ _ := .unit
  decode _ := fun v => match v with | .unit => some () | _ => none
  values_correct := by decide
  kernel _ _ _ := true
  kernel_correct := by decide
  taskValues _ := .unit
  task_correct := by decide
  layers _ _ _ := true
  layers_correct := by decide

/-- Constant source observations are legitimate analysis, with zero capture. -/
def constantAnalysis : Application (@finite_reading_has_fiber.{0}) where
  evidence := .typed {
    source := source
    plan := plan
    acquisition := .finite constantDomain constantPresentation }

/-- The readout image is a lawful quotient, with its own two-state domain. -/
abbrev quotientDomain : Domain source.{0} where
  parameter := threeDomain.parameter
  State := Bool
  readout _ b := b
  scope := .quotient threeReading (by
    intro b
    cases b
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩) (fun _ _ => rfl)

abbrev quotientPresentation : FinitePresentation plan quotientDomain where
  stateFintype := inferInstanceAs (Fintype Bool)
  stateDecidableEq := inferInstanceAs (DecidableEq Bool)
  enumeration := { states := [false, true], nodup := by decide, complete := by decide }
  values _ := ![.bool false, .bool true]
  decode _ := fun v => match v with | .bool b => some b | _ => none
  values_correct := by decide
  kernel _ := ![![true, false], ![false, true]]
  kernel_correct := by decide
  taskValues := ![.bool false, .bool true]
  task_correct := by decide
  layers _ := ![![true, false], ![false, true]]
  layers_correct := by decide

def quotientAnalysis : Application (@finite_reading_has_fiber.{0}) where
  evidence := .typed {
    source := source
    plan := plan
    acquisition := .finite quotientDomain quotientPresentation }

/-- Restricting to the false-reading fiber explicitly changes the counted domain. -/
abbrev restrictedDomain : Domain source.{0} where
  parameter := threeDomain.parameter
  State := {x : Fin 3 // x ≠ 1}
  readout _ x := threeReading x.val
  scope := .restriction (fun x => x ≠ 1) (Equiv.refl _) (fun _ _ => rfl)

abbrev restrictedPresentation : FinitePresentation plan restrictedDomain where
  stateFintype := inferInstanceAs (Fintype {x : Fin 3 // x ≠ 1})
  stateDecidableEq := inferInstanceAs (DecidableEq {x : Fin 3 // x ≠ 1})
  enumeration := {
    states := [⟨0, by decide⟩, ⟨2, by decide⟩]
    nodup := by decide
    complete := by decide }
  values _ _ := .bool false
  decode _ := fun v => match v with | .bool b => some b | _ => none
  values_correct := by decide
  kernel _ _ _ := true
  kernel_correct := by decide
  taskValues _ := .bool false
  task_correct := by decide
  layers _ _ _ := true
  layers_correct := by decide

def restrictedAnalysis : Application (@finite_reading_has_fiber.{0}) where
  evidence := .typed {
    source := source
    plan := plan
    acquisition := .finite restrictedDomain restrictedPresentation }

/-- The entire dependent source is retained; a named infinite fiber has no
finite pair count or rate. This is not a finite-law or FIB contract. -/
noncomputable def infiniteAnalysis : Application.{1,0,0,0,0,0} (@finite_reading_has_fiber.{0}) where
  evidence := .typed {
    source := source
    plan := plan
    acquisition := .infinite ⟨Nat, Bool, fun n => n % 2 == 1⟩ inferInstance }

/-- No finiteness claim about the universal family is required for ingress. -/
def familyAnalysis : Application.{u+1,u,0,u,0,0} (@finite_reading_has_fiber.{u}) where
  evidence := .typed {
    source := source
    plan := plan
    acquisition := .unavailable "No complete finite presentation of the selected family was supplied" }

end Reg.D5.S0.Diagonal.PigeonholeFiber
