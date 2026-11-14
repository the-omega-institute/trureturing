import D5.S3.Quantum.Routing.HannSignedCertificate
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder

namespace Reg.D5.S3.Quantum.Routing.HannSignedCertificate

open _root_.D5.S3.Quantum.Routing
open _root_.D5.S3.Quantum.Routing.HannSpatialQram
open _root_.D5.S3.Quantum.Routing.HannRouterProfiles (Router loadedLabel)
open _root_.D5.S3.Quantum.Routing.HannSignedCertificate
open _root_.D5.S3.Quantum.Routing.ReversibleQram (Address)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun n => Router n → ℝ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ n q => (outputs n q).dimension) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def sourceLaw (R : Realization signature) : Prop :=
  ∀ (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v) (hq' : ∀ v, q v ≤ 1) (bus : Qutrit),
    Module.finrank ℂ (LinearMap.range (synthesis n q bus)) = R.readout () n q ∧
    (outputs n q).kernel.length = 2 ^ n - (outputs n q).dimension ∧
    (vacuumRecord n q ∈ LinearMap.range (synthesis n q bus) ↔ (outputs n q).flag = true) ∧
    (∀ u, (outputs n q).representative = some u → synthesis n q bus u = vacuumRecord n q) ∧
    (∀ x, synthesis n q bus x = 0 ↔
      ∃! α : Fin (outputs n q).kernel.length → ℂ,
        x = ∑ i, α i • (outputs n q).kernel.get i) ∧
    (∀ a b, standardGram n q bus a b =
      ((∏ v, if loadedLabel n a bus v = loadedLabel n b bus v then 1 else q v : ℝ) : ℂ)) ∧
    densityGram n q bus = standardGram n q bus ∧
    LinearMap.ker (densityGram n q bus).mulVecLin = LinearMap.ker (synthesis n q bus) ∧
    (densityGram n q bus).rank = (outputs n q).dimension

abbrev arena : Arena := ⟨signature, sourceLaw⟩

private theorem rejected_law : ¬ sourceLaw rejected := by
  intro h
  have hzero := (h 0 (fun _ => 0) (by intro v; exact v.elim)
    (by intro v; exact v.elim) Qutrit.wait).1
  have hone := (signed_event 0 (fun _ => 0) (by intro v; exact v.elim)
    (by intro v; exact v.elim) Qutrit.wait).1
  change Module.finrank ℂ (LinearMap.range (synthesis 0 (fun _ => 0) Qutrit.wait)) = 0
    at hzero
  change Module.finrank ℂ (LinearMap.range (synthesis 0 (fun _ => 0) Qutrit.wait)) = 1
    at hone
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, outputs, step, restrict]

def family : Registration arena (type_of% signed_event) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨signed_event, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity sourceLaw actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    signed_event (Realization signature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.HannSignedCertificate.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.HannSignedCertificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ n q => (outputs n q).dimension) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Routing.HannSignedCertificate
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end Reg.D5.S3.Quantum.Routing.HannSignedCertificate
