import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.LatticeNullFrameExistence
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeLightConeCoordinates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
/- Faithful source-family attempts. The conditional assemblies do not supply
whole-family variation, role sensitivity, observational dependence or native
source-selection evidence. They are not declared_validated registrations. -/
namespace Reg.D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
namespace OriginalCurrent
structure Params where
  D : LatticeData
  F : NullFrame D
  t : ℕ
  B : Module.Basis (Fin t) ℂ F.K
  u : E D
  m : ℤ
abbrev signature : Signature where
  Params := Params
  State p := Carrier p.D
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Charge p.D →₀ PolynomialCoordinates (NullFrame.Label p.t)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role p v => if role then
    coordinateMode (p.F.completeBasis p.B) p.u p.m (p.F.allChargeEquiv p.B v)
    else p.F.allChargeEquiv p.B (a p.u p.m v))
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {D : LatticeData} (F : NullFrame D) {t : ℕ}
    (B : Module.Basis (Fin t) ℂ F.K) (u : E D) (m : ℤ) (v : Carrier D),
    r.readout false ⟨D,F,t,B,u,m⟩ v = r.readout true ⟨D,F,t,B,u,m⟩ v

theorem source_bridge : (type_of% (@NullFrame.original_carrier_all_charges)) ↔
    arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual :=
  source_bridge.mp (@NullFrame.original_carrier_all_charges)

def registrationAttempt (variation : Variation arena actual)
    (sensitivity : Sensitivity arena actual)
    (dependence : ObservationalDependence signature actual) :
    Contract.Registration (@NullFrame.original_carrier_all_charges) (Realization signature) Params Bool := {
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates.OriginalCurrent.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates.OriginalCurrent.registrationAttempt
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨{
    actual := actual
    bridge := source_bridge
    variation := variation
    sensitivity := sensitivity
    dependence := dependence }⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end OriginalCurrent
namespace Frequency
structure Params where
  D : LatticeData
  F : NullFrame D
  t : ℕ
  B : Module.Basis (Fin t) ℂ F.K
  n : ℕ
abbrev signature : Signature where
  Params := Params
  State p := Oscillator p.D
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role p P => if role then
    MvPolynomial.IsWeightedHomogeneous frequencyWeight (p.F.coordinateEquiv p.B P) p.n
    else MvPolynomial.IsWeightedHomogeneous (oscillatorWeight p.D) P p.n)
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {D : LatticeData} (F : NullFrame D) {t : ℕ}
    (B : Module.Basis (Fin t) ℂ F.K) (P : Oscillator D) (n : ℕ),
    r.readout true ⟨D,F,t,B,n⟩ P ↔ r.readout false ⟨D,F,t,B,n⟩ P

theorem source_bridge : (type_of% (@NullFrame.frequency_grading)) ↔
    arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := source_bridge.mp (@NullFrame.frequency_grading)

def registrationAttempt (variation : Variation arena actual)
    (sensitivity : Sensitivity arena actual)
    (dependence : ObservationalDependence signature actual) :
    Contract.Registration (@NullFrame.frequency_grading) (Realization signature) Params Bool := {
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates.Frequency.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates.Frequency.registrationAttempt
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨{
    actual := actual
    bridge := source_bridge
    variation := variation
    sensitivity := sensitivity
    dependence := dependence }⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Frequency
end Reg.D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
