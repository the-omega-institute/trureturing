import D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice
open _root_.D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechCongruence
open _root_.D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechBasis
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open scoped BigOperators Matrix

abbrev signature := Reg.Support.SingleDependentReadout.signature Coordinates
  (fun _ => Coordinates) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ left right => bilinear data left right) (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ left right : Coordinates,
    8 * observation.readout () left right =
      ∑ axis, (basisMatrix *ᵥ left) axis * (basisMatrix *ᵥ right) axis

theorem source_bridge : (type_of% (@charge_pairing_scaled)) ↔ arena.Law actual := by
  constructor <;> intro source left right <;> exact source left right

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨charge, nonzero, attained⟩ := minimum_attained
  have impossible := law charge charge
  have scaled := charge_pairing_scaled charge charge
  rw [attained] at scaled
  change 8 * (0 : ℤ) = _ at impossible
  omega

theorem dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨charge, nonzero, attained⟩ := minimum_attained
  refine ⟨charge, 0, charge, ?_⟩
  change bilinear data charge 0 ≠ bilinear data charge charge
  rw [attained]
  norm_num [bilinear]

def familyRegistration : Registration arena (type_of% (@charge_pairing_scaled)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp charge_pairing_scaled, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def charge_pairing_scaled_registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@charge_pairing_scaled)
      (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice.charge_pairing_scaled.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ left right => bilinear data left right) (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice
