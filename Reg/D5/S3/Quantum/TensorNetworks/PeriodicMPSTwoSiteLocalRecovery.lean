import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteLocalRecovery

/-! Source-bound registration of the local decoder's coordinate equality. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteLocalRecovery

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteDifferential (chart)
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteLocalRecovery
open LeanInformationAudit Set
open scoped Matrix.Norms.Elementwise

noncomputable section

private abbrev Coord := Fin 4 → ℂ
private abbrev Bits := Fin 2 × Fin 2
private abbrev Density := Matrix Bits Bits ℂ

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Coord) (fun _ => Coord → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ decoded target => decoded = target) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : ℕ,
    ∃ (a : ℂ) (x : Coord) (U : Set Coord) (decode : Density → Coord) (L : ℝ),
      IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, 0 < twoMass (chart a y) r) ∧
      InjOn (fun y => normalizedTwo (chart a y) r) U ∧
      (∀ y ∈ U, R.readout () () (decode (normalizedTwo (chart a y) r)) y) ∧
      0 ≤ L ∧ ∀ y ∈ U, ∀ z ∈ U,
        ‖y - z‖ ≤ L * ‖normalizedTwo (chart a y) r - normalizedTwo (chart a z) r‖

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, x, _, _, _, _, hx, _, _, hinverse, _, _⟩ := h 0
  exact hinverse x hx

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hconstant : (fun _ : Fin 4 => (1 : ℂ)) = fun _ => 0 :=
    (congrFun h (fun _ => 0)).mp rfl
  exact one_ne_zero (congrFun hconstant 0)

def recoveryFamily : Registration arena (type_of% @normalized_local_recovery) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalized_local_recovery, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def recoveryAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@normalized_local_recovery) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteLocalRecovery.normalized_local_recovery.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteLocalRecovery.recoveryFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨recoveryFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ decoded target => decoded = target) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteLocalRecovery
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms recoveryAudit

end

end Reg.D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteLocalRecovery
