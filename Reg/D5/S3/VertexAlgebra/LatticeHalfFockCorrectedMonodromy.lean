import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectedMonodromy

/-! Exact source-family audits for the unchanged coordinate identities. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedMonodromy

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeHalfFockCorrectedField LatticeHalfFockFiniteCorrection LatticeInvolution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
open scoped BigOperators TensorProduct

noncomputable section

private theorem corr_one (D : LatticeData) (a : Charge D) :
    Corr D a 1 = Finsupp.single 0 1 := by
  have h := Corr_monomial_enumeration D a 0 []
    (by simp [LatticeAllStateField.occurrences])
  have h' : Corr D a 1 = shiftCoefficients D (1 : Polynomial (Oscillator D)) := by
    simpa [correctionWord] using h
  rw [h']
  apply Finsupp.ext
  intro n
  change (1 : Polynomial (Oscillator D)).coeff n = (Finsupp.single 0 1) n
  simp [Polynomial.coeff_one, Finsupp.single_apply, eq_comm]

namespace Normal
abbrev Parameter := Σ D : LatticeData, Σ _a : Charge D, Oscillator D
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun _ => ℤ) (fun _ => ℂ)
def actual : Realization signature := realize signature
  (fun _ _ e => (-1 : ℂ)^e) (fun empty => nomatch empty)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) (e : ℤ),
    (polynomialField D hu (-a) (sigma D p)).coeff e =
      readout.readout () ⟨D, a, p⟩ e • (polynomialField D hu a p).coeff e
theorem source_bridge : (type_of% (@normal_polynomial_coordinate_monodromy)) ↔
    arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit 0 1 0
  have zero : (polynomialField hyperbolic hyperbolic_unit 0 1).coeff 0 = 0 := by
    simpa [rejected, realize] using bad
  rw [probe_polynomial_one] at zero
  exact probe_leading (by
    simpa only [chargedField, HVertexOperator.coeff_of_coeff, LinearMap.zero_apply] using
      LinearMap.congr_fun zero probeState)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic, 0, 1⟩, 0, 1, ?_⟩
  norm_num [actual, realize]

def familyRegistration : Registration arena (type_of% (@normal_polynomial_coordinate_monodromy)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp normal_polynomial_coordinate_monodromy, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@normal_polynomial_coordinate_monodromy) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField.normal_polynomial_coordinate_monodromy "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedMonodromy.Normal.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockCorrectedMonodromy
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Normal

namespace Correction
abbrev Parameter := Σ D : LatticeData, Charge D
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun p => Oscillator p.1) (fun p => ℕ →₀ Oscillator p.1)
def actual : Realization signature := realize signature
  (fun _ p q => Finsupp.mapRange.linearMap (sigmaLinear p.1) (Corr p.1 p.2 q))
  (fun empty => nomatch empty)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (a : Charge D) (p : Oscillator D),
    Corr D (-a) (sigma D p) = readout.readout () ⟨D, a⟩ p
theorem source_bridge : (type_of% (@Corr_sigma)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic 0 1
  have zero : (Finsupp.single 0 (1 : Oscillator hyperbolic) : ℕ →₀ Oscillator hyperbolic) = 0 := by
    simpa [rejected, realize, corr_one] using bad
  have value := congrArg (fun f : ℕ →₀ Oscillator hyperbolic => f 0) zero
  exact (one_ne_zero : (1 : Oscillator hyperbolic) ≠ 0) (by simpa using value)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic, 0⟩, 0, 1, ?_⟩
  intro equality
  have value := congrArg (fun f : ℕ →₀ Oscillator hyperbolic => f 0) equality
  exact (one_ne_zero : (1 : Oscillator hyperbolic) ≠ 0)
    (by simpa [actual, realize, corr_one, sigmaLinear,
      Finsupp.mapRange.linearMap_apply] using value.symm)

def familyRegistration : Registration arena (type_of% (@Corr_sigma)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp Corr_sigma, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Corr_sigma) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField.Corr_sigma "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedMonodromy.Correction.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockCorrectedMonodromy
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Correction

namespace Full
abbrev Parameter := Σ D : LatticeData, Carrier D
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun _ => ℤ) (fun _ => ℂ)
def actual : Realization signature := realize signature
  (fun _ _ e => (-1 : ℂ)^e) (fun empty => nomatch empty)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (u : Carrier D) (e : ℤ),
    (correctedField D hu (theta D u)).coeff e =
      readout.readout () ⟨D, u⟩ e • (correctedField D hu u).coeff e
theorem source_bridge : (type_of% (@correctedField_theta)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law hyperbolic hyperbolic_unit probeSource 0
  have good := correctedField_theta hyperbolic hyperbolic_unit probeSource 0
  have zero : (correctedField hyperbolic hyperbolic_unit probeSource).coeff 0 = 0 := by
    simpa [rejected, realize] using good.symm.trans bad
  rw [probe_source_field] at zero
  exact probe_leading (by
    simpa only [chargedField, HVertexOperator.coeff_of_coeff, LinearMap.zero_apply] using
      LinearMap.congr_fun zero probeState)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic, probeSource⟩, 0, 1, ?_⟩
  norm_num [actual, realize]

def familyRegistration : Registration arena (type_of% (@correctedField_theta)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp correctedField_theta, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@correctedField_theta) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField.correctedField_theta "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedMonodromy.Full.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockCorrectedMonodromy
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Full

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedMonodromy
