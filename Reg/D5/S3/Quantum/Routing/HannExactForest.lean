import D5.S3.Quantum.Routing.HannExactForest
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-owner audits and explicit dependence boundaries for the exact node lift. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Quantum.Routing.HannExactForest

open _root_.D5.S3.Quantum.Routing
open _root_.D5.S3.Quantum.Routing.HannSpatialQram (Qutrit)
open _root_.D5.S3.Quantum.Routing.HannRouterProfiles (Router)
open _root_.D5.S3.Quantum.Routing.HannSignedCertificate
open _root_.D5.S3.Quantum.Routing.HannExactForest
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ Coeff Coeff

def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def sourceLaw (R : Realization signature) : Prop :=
  ∀ (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v ∧ q v ≤ 1) (x : Coeff n) (z : ℂ),
    synthesis n q bus (R.readout () n x) = z • vacuumRecord n q ↔
      ∃ c : Node n → ℂ, c (root n) = z ∧
        (complexMatrix n q).mulVec (coordinates n x c) = 0

abbrev arena : Arena := ⟨signature, sourceLaw⟩

private theorem rejected_law : ¬ sourceLaw rejected := by
  intro h
  let q : Router 0 → ℝ := fun v => v.elim
  have hq : ∀ v, -(1 / 2 : ℝ) ≤ q v ∧ q v ≤ 1 := by intro v; exact v.elim
  have hh := h 0 q Qutrit.wait hq (fun _ => 1) 0
  have hz : synthesis 0 q Qutrit.wait (rejected.readout () 0 (fun _ => 1)) =
      (0 : ℂ) • vacuumRecord 0 q := by
    change synthesis 0 q Qutrit.wait 0 = (0 : ℂ) • vacuumRecord 0 q
    rw [map_zero, zero_smul]
  have lift := hh.mp hz
  have impossible := (relation_iff_matrix_kernel 0 q Qutrit.wait hq (fun _ => 1) 0).mpr lift
  have he := congrFun impossible (fun v => v.elim)
  norm_num [synthesis, record, vacuumRecord] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h ()
  exact zero_ne_one hh

def family : Registration arena (type_of% relation_iff_matrix_kernel) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨relation_iff_matrix_kernel, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity sourceLaw actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    relation_iff_matrix_kernel (Realization signature) (ℕ → Type) Unit where
  unitName := `Reg.D5.S3.Quantum.Routing.HannExactForest.Relation.unit
  realizationName := `Reg.D5.S3.Quantum.Routing.HannExactForest.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Routing.HannExactForest
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace ForestObservation

abbrev parameter := Σ n : ℕ, Router n → ℝ
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature parameter
  (fun _ => Unit) (fun p => SimpleGraph (Row p.1 p.2 ⊕ Variable p.1))

def actual : Realization signature :=
  realize signature (fun _ p _ => support p.1 p.2) (fun e => nomatch e)

/-- A graph-valued readout with all rates in parameters is constant in its Unit state. -/
theorem no_observational_dependence : ¬ ObservationalDependence signature actual := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  exact hxy (congrArg (actual.readout () p) (Subsingleton.elim x y))

end ForestObservation

#print axioms family
#print axioms relation_iff_matrix_kernel
#print axioms support_is_acyclic

end Reg.D5.S3.Quantum.Routing.HannExactForest
